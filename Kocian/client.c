#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <signal.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <time.h> //sleep
#include <stdbool.h>
#include <regex.h>      //per @<to>:<msg>
#include <pthread.h>

#define BUFACK_SIZE 4          /* 3 char + terminatore */
#define BUFSIZE 4096           /* massima grandezza del payload */
#define MAX_CHARS_TO_READ 4095 /* massimo numero di caratteri da leggere da input */

const char *ack = "ACK"; /* concordato con il server */


/* argomenti da passare al thread di lettura */
typedef struct thread_args
{
    bool busy;            /* indica se la cella dell'array è assegnata a un thread in uso */
    int socket;           /* socket da gestire (condivisa) */
    pthread_t tid_parent; /* thread id del processo padre*/

} thread_args_t;

/* variabili per la gestione del thread di lettura */
pthread_t reading_thread; /* costantemente in ascolto di nuovi messaggi ricevuti da mostrare al client */
thread_args_t thread_arg; /* struct contenente gli argomenti da passare al thread di lettura */
pthread_attr_t attr;      /* rendo esplicitamente joinable il thread */
int err_thread;           /* valore dell'errore ritornato nella creazione/join del thread */

/* - - - - - - - - - - - - - - - - - -  */

/* variabili per la creazione del socket e la connessione con il server */
int sock;
struct sockaddr_in server_addr; /* AF_INET + porta 16 bit + IP 32 bit */


/*
    Stampa la stringa passata come parametro per n volte (con \n finale)
*/
void print_nstr(char *string_to_print, unsigned int n)
{
    for (size_t i = 0; i < n; i++)
        printf("%s", string_to_print);
    printf("\n");
}

/* 
    Questa funzione analizza il buffer passato come parametro e fin tanto che non trova un carattere 
    terminatore, <newline> o <carriage return> (Windows compliant) incrementa il valore del puntatore
    al buffer. Una volta trovato il carattere incriminato, lo setta come carattere terminatore
*/
void remove_end_new_line(char *s)
{
    while (*s && *s != '\n' && *s != '\r')
    {
        s++;
    }

    *s = 0; /* aggiungo il terminatore al posto del \n o \r */
}

/*
    Stampa su console il prompt_text (se prompt_text == "\0" non viene stampato nulla),
    legge la stringa inserita (escluso <newline> e <carriage return>)
    dallo stream passato come parametro. 
    `input_user` è un buffer di al massimo BUFSIZE byte, incluso il terminatore di stringa.
    Ritorna il numero di caratteri letti (escluso il \n).
*/
size_t input(char *prompt_text, char input_user[])
{

    /* se viene passato come parametro \0 allora non viene stampato il prompt */
    if (strcmp(prompt_text, "\0") != 0)
    {
        printf("%s", prompt_text);
    }

    /* char* string_readed = */ fgets(input_user, MAX_CHARS_TO_READ, stdin);

    // printf("fgets [%s]\n", string_readed); /* DEBUG */
    // printf("Hai scritto: [%s]\n", input_user);  /* DEBUG*/

    remove_end_new_line(input_user);

    // printf("dopo remove_end_new_line ==> Hai scritto: [%s]\n", input_user);  /* DEBUG*/

    return strlen(input_user);
}

/*  
    Legge il messaggio ricevuto e lo memorizza nel buffer `buffer`.
    Il buffer puntato da `buffer` deve essere stato opportunamente inizializzato per ospitare massimo BUFSIZE caratteri 
    Ritorna il numero di byte letti.
    Ritorna 0 se l'altro lato della connessione ha chiuso il socket.
    In caso di errore ritorna -1.
*/
ssize_t sread(int socket, char buffer[])
{
    /*
        If your other side exited gracefully, you will get 0 from recv() at some point.
        If the connection was somehow lost, you may also get -1 and checking for appropriate
        errno would tell you if the connection was lost of some other error occured.
    */
    ssize_t c_read = 0;

    /* pulisco la memoria così da avere il terminatore alla fine ed evitare caratteri random letti dalla memoria */
    memset(buffer, 0, BUFSIZE);

    /* leggo dal socket con la recv() così da usare il flag MSG_WAITALL e bloccare la lettura fin quando non vengono letti tutti i byte richiesti */
    c_read = recv(socket, buffer, BUFSIZE - 1, MSG_WAITALL); /* -1 così da avere alla fine il terminatore di stringa */

    // printf("sread==> [%s] buffer\n", buffer); /* DEBUG */

    /* se il numero di byte letti corrisponde al numero di byte che ci si aspettava di leggere è tutto ok */
    if (c_read > 0)
    {
        // printf("lettura ok!\n"); /* DEBUG */

        return c_read;
    }
    else if (c_read == 0) /* l'altro lato della connessione ha chiuso il socket */
    {
        return 0;
    }
    else /* c'è stato un errore */
    {
        return -1;
    }
}

/*  
   Funge da wrapper per le operazioni di scrittura.
*/
ssize_t swrite(int socket, void *buffer)
{
    ssize_t byte_writed = 0; /* numero di byte scritti */

    /* invio il messaggio contenuto in *buffer */
    byte_writed = write(socket, buffer, BUFSIZE - 1);
    if (errno == EPIPE) /* si è provato a scrivere sul socket con la parte remota chiusa */
    {
        perror("swrite() -> write() {buffer} errno == EPIPE"); /* DEBUG */
        return -2;
    }
    else if (byte_writed < 0)
    {
        perror("swrite() -> write() {buffer} < 0 "); /* DEBUG */
        return -1;
    }
    else
    {
        return byte_writed;
    }
}

/*
    Ritorna true se il formato dell'input è corretto, altrimenti torna false.
*/
bool format_valid(char *input)
{

    regex_t regex;

    /*
        Questa regex matcha qualsiasi stringa che inizia con un @ (^@), ha uno o più caratteri (.+)
        poi ci sono i : e infine ha uno o più caratteri (.+$). Per i quantificatori + e ? è necessario il flag REG_EXTENDED.
    */
    regcomp(&regex, "^@.+:.+", REG_EXTENDED);

    if (regexec(&regex, input, 0, NULL, 0) == 0)
    {
        /* c'è pattern matching */
        return true;
    }
    else
    {
        return false;
    }
}

/*
    Da usare solo con input validato. Configura il mittente e il messaggio per una lunghezza di massimo BUFSIZE.
    Ritorna 0 in caso di successo, -1 altrimenti.
*/
int get_tokens(char input_user[], char receiver[], char msg[])
{
    char input_original[BUFSIZE];
    strncpy(input_original, input_user, BUFSIZE - 1); /* BUFSIZE - 1 così da far inserire il terminatore */
    // printf("input_original [%s]\n", input_original);  /* DEBUG */

    /* per estrarre il destinatario lavoro sull'input passato */
    char *token_at = strtok(input_user, ":"); /* ottengo @<To> */
    token_at = strtok(input_user, "@");
    strncpy(receiver, token_at, BUFSIZE - 1);

    /* per estrarre il messaggio lavoro sulla copia dell'input */
    char *token_column = strtok(input_original, ":"); /* ottengo @<To> */
    token_column = strtok(NULL, "");                  /* ottengo il messaggio, anche se l'utente inizia un messaggio con ":" */
    strncpy(msg, token_column, BUFSIZE - 1);

    // printf("msg [%s]\n",msg); //DEBUG
    // printf("receiver [%s]\n",receiver); //DEBUG

    return 0;
}

/*
    Legge il messaggio ricevuto sul socket `sock` e lo mostra al client.
    Ritorna -1 in caso di errore (es: connessione persa).
    Ritorna -2 se è stata interrotta da un segnale di tipo SIGINT.
    Ritorna 0 altrimenti.
*/
int read_message_received(int sock)
{
    ssize_t return_sread = 0; /* codice di ritorno della sread*/
    int return_code = 0;      /* codice di ritorno */
    char msg[BUFSIZE];        /* messaggio ricevuto */

    // printf("sono nella read_message_received\n"); /* DEBUG */
    return_sread = sread(sock, msg);
    // printf("msg [%s]\n", msg); /* DEBUG */
    if (return_sread == 0)
    {
        // fprintf(stderr, "Error: read_message_received() -> sread() connection resetted by peer\n"); /* DEBUG */
        return_code = -1;
    }
    else if (return_sread == -1)
    {
        // fprintf(stderr, "Error: read_message_received() -> sread() generic error\n"); /* DEBUG */
        return_code = -1;
    }
    else if (return_sread == -2)
    {
        // fprintf(stderr, "Error: read_message_received() -> sread() SIGINT received\n"); /* DEBUG */
        return_code = -2;
    }
    else
    {
        // printf("[+] C'È UN NUOVO MESSAGGIO\n"); /* DEBUG */
        printf("\n");
        print_nstr("- ", 25);
        printf("%s\n", msg);
        print_nstr("- ", 25);
        return_code = 0;
    }

    return return_code;
}

/*
    Gestore del segnale SIGINT
*/
void handler_sigint(int signo)
{
    (void)signo; /* per evitare warning */

    close(sock); /* può essere stata chiusa dal thread read */

    printf("\n\n");
    print_nstr("#", 30);
    printf("\n\tGoodbye\n\n");
    print_nstr("#", 30);
    exit(EXIT_SUCCESS);
}

/*
    Questa funzione si occupa di controllare continuamente il buffer dei messaggi ricevuti, 
    con un meccanismo di condition variable.
*/
void *handler_read(void *threadarg)
{

    thread_args_t *args = (thread_args_t *)threadarg; /* ottengo gli argomenti passati come parametro */
    bool *busy = (bool *)&args->busy;                 /* flag per riusare le celle degli array solo se non più occupati a fare qualcosa */
    int *socket = (int *)&args->socket;               /* socket da gestire */
    pthread_t tid = (pthread_t)args->tid_parent;      /* thread id del processo padre */
    (void)tid;                                        //evita warning
    bool closed_session = false;
    int rdmsg = 0;

    /* fin tanto che non viene chiusa la connessione o non c'è errore, controllo se ci sono eventuali nuovi messaggi */
    while (!closed_session)
    {
        // printf("THREAD READ\n"); /* DEBUG */

        rdmsg = read_message_received(*socket); /* BLOCCANTE ma il socket è full duplex quindi posso leggere e scrivere contemporaneamente */
        // printf("rdmsg = %d\n", rdmsg); /* DEBUG */
        if (rdmsg == -1)
        {
            /* connessione terminata */
            printf("[+] Server have closed connection\n");
            closed_session = true;
        }
        // else
        // {
        //     printf("ritorno dalla read_message_received() %d\n", rdmsg);
        // }

    } //fine while sessione

    /* una volta terminata la sessione del client, chiudo il socket */
    close(*socket);
    /* setto il thread come non più occupato */
    *busy = false;

    pthread_exit(NULL);
}


int main(int argc, char *argv[])
{

    /* variabili per conservare gli argomenti passati */
    char IP_SERVER[INET_ADDRSTRLEN];
    char USERNAME[BUFSIZE];
    uint16_t PORT;

    /* variabili per la gestione dei segnali */
    struct sigaction sa;

    /* contatore tentativi connect() */
    ssize_t connect_try = 0;

    /* Controllo argomenti */
    if (argc != 4)
    {
        fprintf(stderr, "Errore, Uso: %s <hostID> <username> <portID>\n", argv[0]);
        exit(EXIT_FAILURE);
    }
    else
    {
        /* configuro i parametri del client in base all'input */
        strncpy(IP_SERVER,argv[1],INET_ADDRSTRLEN);
        /* lo username può essere di massimo 4095 + terminatore, dimensione concordata con il server */
        if (strlen(argv[2]) > BUFSIZE - 1)
        {
            fprintf(stderr, "Error <username>: max 4096 characters.\n");
            exit(EXIT_FAILURE);
        }
        else
        {
            strncpy(USERNAME,argv[2],4095);
        }

        PORT = atoi(argv[3]);
    }

    /* configurazione dei segnali */
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_RESTART;
    sa.sa_handler = handler_sigint;

    if (sigaction(SIGINT, &sa, NULL) != 0)
    {
        perror("main() -> sigaction()");
        exit(EXIT_FAILURE);
    }

    for (;;) /* " The program may not crash if the connection fails. " */
    {

        char input_user[BUFSIZE];  /* input dell'utente */
        char receiver[BUFSIZE];    /* destinatario del messaggio*/
        char msg[BUFSIZE];         /* messaggio da inviare */
        ssize_t return_swrite = 0; /* codice di ritorno della swrite */
        int err_connect = 0;
        bool end = false;

        /* resetto lo spazio di memoria che ospiterà la struct del thread di lettura */
        memset(&reading_thread, 0, sizeof(reading_thread));

        /* resetto lo spazio di memoria che ospiterà gli argomenti del thread di lettura */
        memset(&thread_arg, 0, sizeof(thread_arg));

        /* faccio il reset al valore di default della struct */
        pthread_attr_init(&attr);

        /* rendo il thread di lettura creato con questo attributo, joinable */
        if (pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE) != 0)
        {
            perror("pthread_attr_setdetachstate()");
            exit(EXIT_FAILURE);
        }

        /* Configuro il thread come non occupato. */
        thread_arg.busy = false;

        /* creo il socket */
        if ((sock = socket(PF_INET, SOCK_STREAM, 0)) < 0) /* protocolli internet IPv4 + socket TCP + protocollo di default del SO */
        {
            perror("socket()");
            exit(EXIT_FAILURE);
        }

        /* Costruzione dell'indirizzo */
        memset(&server_addr, 0, sizeof(server_addr));
        server_addr.sin_family = AF_INET;
        server_addr.sin_port = htons(PORT);
        /* configuro l'indirizzo IPv4 nella struct, IP deve essere in dotted-decimal */
        if (inet_pton(AF_INET, IP_SERVER, &server_addr.sin_addr) < 0)
        {
            perror("inet_pton()");
            exit(EXIT_FAILURE);
        }

        /* Provo a fare la connect() con il server */
        if ((err_connect = connect(sock, (struct sockaddr *)&server_addr, sizeof(server_addr))) < 0)
        {
            printf("Tentativo #%zu: connessione con il server non riuscita\n", connect_try++);
            perror("connect()");
            sleep(2);
            continue; /* devo riprovare la connessione nella iterazione successiva */
        }
        /* Scambio dati con il server: */

        /* 
            From the official POSIX reference:
            If fildes refers to a socket, write() shall be equivalent to send() with no flags set.

            Stesso discorso per la read() e la recv().
        */

        /* invio lo username */
        if ((return_swrite = swrite(sock, USERNAME)) == -2)
        {
            fprintf(stderr, "Error: main() -> swrite() {USERNAME} connection resetted by peer\n"); /* DEBUG */
            continue;
        }
        else if (return_swrite == -1)
        {
            fprintf(stderr, "Error: main() -> swrite() {USERNAME} generic error\n"); /* DEBUG */
            continue;
        }

        // printf("return_swrite USERNAME %ld\n", return_swrite); /* DEBUG */

        printf("connected.\n");

        /* Una volta connesso al server, creo il thread di lettura che dovrà occuparsi di leggere i messaggi in arrivo */
        /* inizializzo gli argomenti per il nuovo thread da creare */
        thread_arg.busy = true;   /* thread di lettura che stiamo creando è occupato */
        thread_arg.socket = sock; /* socket dalla quale leggere i messaggi ricevuti */

        /* una volta configurati i parametri da passargli, creo il thread di sola lettura del buffer */
        if ((err_thread = pthread_create(&reading_thread, &attr, handler_read, (void *)&thread_arg)) != 0)
        {
            fprintf(stderr, "ERROR: return code from pthread_create() is %d\n", err_thread);
            end = true;
            continue;
        }

        /* distruggo lo spazio usato per gli attributi dei thread */
        pthread_attr_destroy(&attr);

        /* stacco il thread di lettura così da poter servire l'utente e gestire contemporaneamente l'input */
        err_thread = pthread_detach(reading_thread);
        if (err_thread)
        {
            fprintf(stderr, "ERROR: return code from pthread_detach() is %d\n", err_thread);

            end = true;
        }

        /*
            Per mandare un messaggio ad un utente bisogna usare la sintassi @<To>:<message>
            Da questo punto in poi, all'interno del ciclo while, l'accesso alla socket deve essere
            regolato e sincronizzato tra i 2 thread 
        */
        while (!end)
        {

            print_nstr("_", 40);

            input("=>", input_user); /* bloccante in attesa di un input */

            /*
                se il formato rispetta @<to>:message allora estraggo destinatario e messaggio
                e dialogo con il server
            */

            /* 
                Fin tanto che l'utente non inserisce un input, il thread in lettura può continuare ad operare
                e continuare a leggere messaggi sul socket    
            */
            /* prima di iniziare il parsing verifico se la connessione è terminata, e dunque il thread lettore ha chiuso il socket */
            if (!thread_arg.busy)
            {
                close(sock); /* chiudo il socket */
                end = true;  /* devo riaprire un nuovo socket */
            }
            else if (format_valid(input_user))
            {
                if (get_tokens(input_user, receiver, msg) != 0)
                {
                    fprintf(stderr, "Error: main() -> get_tokens()\n"); /* DEBUG */
                    continue;
                }

                /* invio il destinatario del messaggio */
                if ((return_swrite = swrite(sock, receiver)) == -2)
                {
                    fprintf(stderr, "Error: main() -> swrite() {receiver} connection resetted by peer\n"); /* DEBUG */
                    end = true;
                    continue;
                }
                else if (return_swrite == -1)
                {
                    fprintf(stderr, "Error: main() -> swrite() {receiver} generic error\n"); /* DEBUG */
                    continue;
                }

                /* se sono qui, destinatario inviato correttamente */

                printf("destinatario [%s] inviato [%ld]\n", receiver, return_swrite); /* DEBUG */
                
                /* invio il messaggio al server solo se ho ricevuto l'ack sul destinatario */
                if ((return_swrite = swrite(sock, msg)) == -2)
                {
                    fprintf(stderr, "Error: main() -> swrite() {msg} connection resetted by peer\n"); /* DEBUG */
                    end = true;
                    continue;
                }
                else if (return_swrite == -1)
                {
                    fprintf(stderr, "Error: main() -> swrite() {msg} generic error\n"); /* DEBUG */
                    continue;
                }

                //printf("messaggio [%s] inviato [%ld]\n", msg, return_swrite); /* DEBUG */
            }
            else
            {
                fprintf(stderr, "Error: format @<TO>:<MESSAGE>\n");
            }

        } /* fine while invio/lettura messaggi */
        close(sock);
    }

    pthread_exit(NULL);

    return 0;
}
