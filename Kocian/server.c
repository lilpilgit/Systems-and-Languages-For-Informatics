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
#include <arpa/inet.h> //inet_pton
#include <pthread.h>
#include <stdint.h> //uintptr_t
#include <stdbool.h>

#define _XOPEN_SOURCE 700

#define BUFSIZE 4096           /* massima grandezza del payload */
#define MAX_CHARS_TO_READ 4095 /* massimo numero di caratteri da leggere da input */

/* argomenti da passare ad ogni thread */
typedef struct thread_args
{
    size_t thread_index;                /* index del thread nell'array */
    bool busy;                          /* indica se la cella dell'array è assegnata a un thread in uso */
    int socket;                         /* socket da gestire */
    char username[BUFSIZE];             /* username dell'utente gestito */
    char IP_client[INET_ADDRSTRLEN];    /* buffer contenente l'indirizzo ip del client */
    char msg_received[BUFSIZE];         /* buffer contenente i messaggi ricevuti per il client */
    bool msg_received_full;             /* variabile di controllo per sapere se il buffer dei messaggi è pieno */
    pthread_mutex_t mutex_msg_received; /* mutex per accedere al buffer dei messaggi ricevuti in modo esclusivo */
    pthread_cond_t cond_msg_received;   /* condition variable per accedere al buffer dei messaggi ricevuti in modo esclusivo */
} thread_args_t;

/* variabili per la gestione dei thread */
pthread_t threads[SOMAXCONN];              /* potrò gestire fino ad un massimo di SOMAXCONN connessioni contemporanee */
pthread_t reading_threads[SOMAXCONN];      /* ognuno di essi è costantemente in ascolto di nuovi messaggi da inviare al client */
thread_args_t thread_arg_array[SOMAXCONN]; /* array di struct contenenti gli argomenti da passare ad ogni thread */
pthread_attr_t attr;                       /* rendo esplicitamente joinable i thread */
pthread_mutexattr_t attr_mutex;            /* proprietà del mutex */
int err_thread;                            /* valore dell'errore ritornato nella creazione/join del thread */
/* - - - - - - - - - - - - - - - - - -  */

/*
    Se le operazioni sono state effettuate correttamente ritorna 0.
    Altrimenti un numero != 0.
*/
int close_connection_thread(size_t thread_index)
{
    int return_err = 0;
    bool *busy = (bool *)&thread_arg_array[thread_index].busy;           /* flag per riusare le celle degli array solo se non più occupati a fare qualcosa */
    int *socket = (int *)&thread_arg_array[thread_index].socket;         /* socket da gestire */
    char *username = (char *)&thread_arg_array[thread_index].username;   /* username dell'utente gestito, copiato dal processo padre nel buffer del thread */
    char *IP_client = (char *)&thread_arg_array[thread_index].IP_client; /* buffer contenente l'indirizzo ip del client */
    // char *msg_received = (char *)&args->msg_received;                                   /* buffer contenente il messaggio da mostrare al client, allocato dinamicamente */
    pthread_mutex_t *mutex_msg_received = (pthread_mutex_t *)&thread_arg_array[thread_index].mutex_msg_received; /* mutex per accedere al buffer contenente i messaggi ricevuti */
    pthread_cond_t *cond_msg_received = (pthread_cond_t *)&thread_arg_array[thread_index].cond_msg_received;     /* coondition variable per accedere al buffer contenente i messaggi ricevuti */
    /* stampo le info sul client disconnesso */
    printf("%s:%s disconnected\n", IP_client, username);
    /* una volta terminata la sessione del client, chiudo il socket */
    close(*socket);
    /* setto il thread come non più occupato */
    *busy = false;
    /* distruggo il mutex creato nel processo principale */
    return_err = pthread_mutex_destroy(mutex_msg_received);
    /* distruggo la condition variable creata nel processo principale */
    return_err = pthread_cond_destroy(cond_msg_received);
    /* 
        la memoria dove sono contenuti i messaggi ricevuti è stata liberata sicuramente in precedenza nella 
        chiamata a read_message_from_thread_queue() 
    */

    return return_err;
}

/*
    Consente di avere una stampa formattata dei thread per il debug
*/
void info_thread(pthread_t thread, thread_args_t thread_arg)
{
    printf("\n - - - - - - - - - - - - - - - - - - \n");
    printf("\t thread: %ld\n", thread_arg.thread_index); /* id univoco ottenibile anche con pthread_self() */
    printf("- thread_index: %zu\n", thread_arg.thread_index);
    printf("- socket: %d\n", thread_arg.socket);
    printf("- username: %s\n", thread_arg.username);
    printf("- IP_client: %s\n", thread_arg.IP_client);
    printf("\n - - - - - - - - - - - - - - - - - - \n");
}

/* 
    Trova il primo thread disponibile e ritorna l'indice relativo all'interno dell'array thread_arg_array.
    Ritorna -1 in caso di fallimento 
*/
ssize_t find_available_thread(size_t max_number_threads)
{
    /* 
        per trovare il primo thread disponibile, basta cercare nell'array quale ha valore busy = false.
        Dopo aver chiamato la pthread_exit() infatti viene settato a false.    
    */

    for (size_t i = 0; i < max_number_threads; i++)
    {

        if (!thread_arg_array[i].busy)
        {
            // printf("find_available_thread -> thread i:%ld | thread_index: %ld\n", i, thread_arg_array[i].thread_index); /* DEBUG */
            /* trovato! */
            return i;
        }
    }

    return -1;
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
   Funge da wrapper per la operazione di scrittura.
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
    Ritorna l'indice univoco del thread (thread_index) corrispondente allo username passato come parametro.
    dimension è la dimensione dell'array th_args_array.
    th_args_array è l'array contenente le struct con gli argomenti di ogni thread.
    Ritorna -1 in caso di thread non trovato.
*/
ssize_t find_thread_user(char *username, thread_args_t *th_args_array, size_t dimension)
{
    /* con un ciclo for viene analizzato l'intero array fin quando non viene trovato il thread con lo username passato come parametro */
    for (size_t i = 0; i < dimension; i++)
    {
        // printf("th_args_array[i].username [%s]\n", th_args_array[i].username);          /* DEBUG */
        // printf("th_args_array[i].thread_index [%ld]\n", th_args_array[i].thread_index); /* DEBUG */
        if (strcmp(th_args_array[i].username, username) == 0)
        {
            // printf("trovato\n"); //DEBUG
            return th_args_array[i].thread_index;
        }
    }
    return -1;
}

/*
    Scrive msg_to_thread nel buffer thread_arg_array[thread_receiver].msg_received.
    Ritorna -1 in caso di errore o di buffer pieno con altri messaggi.
    Ritorna 0 altrimenti.
*/
int write_message_to_thread_queue(char *msg_to_thread, size_t thread_receiver)
{
    if (thread_arg_array[thread_receiver].msg_received_full == true)
    {
        /* buffer del thread destinatario occupato */
        // printf("buffer del thread utente destinatario [%s] pieno \n", thread_arg_array[thread_receiver].username); /* DEBUG */
        return -1;
    }
    /* se sono qui il buffer del thread ricevente è vuoto e posso scrivere il messaggio */

    strncpy(thread_arg_array[thread_receiver].msg_received, msg_to_thread, BUFSIZE - 1); /* -1 per il terminatore */

    /* imposto il buffer come pieno IMPORTANTE!!!! */
    thread_arg_array[thread_receiver].msg_received_full = true;

    return 0;
}

/*
    QUESTA FUNZIONE DEVE ESSERE CHIAMATA SOLAMENTE DAL PROPRIETARIO DELLA CODA DALLA QUALE SI VA A LEGGERE!
    Legge msg_received dal buffer thread_arg_array[thread_index].msg_received e lo scrive sul socket con l'utente gestito.
    Ritorna -1 in caso di buffer vuoto.
    Ritorna -2 in caso di errore (es: connessione persa)
    Ritorna 0 altrimenti.
*/
int read_message_from_thread_queue(size_t thread_index)
{
    ssize_t return_swrite = 0; /* codice di ritorno della swrite */
    int return_code = 0;       /* codice di ritorno */

    /* controllo se il buffer dei messaggi ricevuti è pieno */
    if (thread_arg_array[thread_index].msg_received_full == false)
    {
        // printf("buffer del thread utente %s vuoto \n", thread_arg_array[thread_index].username); /* DEBUG */
        return -1;
    }

    /* se sono qui il buffer è pieno del messaggio */

    // printf("NUOVO MESSAGGIO PER %s : [%s]\n", thread_arg_array[thread_index].username, thread_arg_array[thread_index].msg_received);
    /* Scrivo sul socket con l'utente che sto gestendo, il messaggio che ho nella coda. Consumo il messaggio */
    return_swrite = swrite(thread_arg_array[thread_index].socket, thread_arg_array[thread_index].msg_received);
    if (return_swrite == -2)
    {
        fprintf(stderr, "Error: read_message_from_thread_queue() -> swrite() connection resetted by peer\n"); /* DEBUG */
        return_code = -2;
    }
    else if (return_swrite == -1)
    {
        fprintf(stderr, "Error: read_message_from_thread_queue() -> swrite() generic error\n"); /* DEBUG */
        return_code = -2;
    }
    else
    {
        // printf("READ_MESSAGE_FROM_THREAD_QUEUE [OK]\n"); /* DEBUG */
        return_code = 0;
    }

    /* pulisco il buffer anche in caso di errore della write al client */

    /* pulisco la memoria così da avere il terminatore alla fine ed evitare caratteri random letti dalla memoria */
    memset(thread_arg_array[thread_index].msg_received, 0, BUFSIZE);

    /* imposto il buffer come vuoto IMPORTANTE!!!! */
    thread_arg_array[thread_index].msg_received_full = false;

    return return_code;
}

/*
    Questa funzione si occupa di controllare continuamente il buffer dei messaggi ricevuti di un utente, 
    con un meccanismo di condition variable.
*/
void *handler_read(void *threadarg)
{
    /* ottengo gli argomenti passati come parametro */
    thread_args_t *args = (thread_args_t *)threadarg;

    size_t *thread_index = (size_t *)&(args->thread_index);
    // bool *busy = (bool *)&args->busy;           /* flag per riusare le celle degli array solo se non più occupati a fare qualcosa */
    // int *socket = (int *)&args->socket;         /* socket da gestire */
    // char *username = (char *)&args->username;   /* username dell'utente gestito, copiato dal processo padre nel buffer del thread */
    // char *IP_client = (char *)&args->IP_client; /* buffer contenente l'indirizzo ip del client */
    // char *msg_received = (char *)&args->msg_received;                                   /* buffer contenente il messaggio da mostrare al client, allocato dinamicamente */
    pthread_mutex_t *mutex_msg_received = (pthread_mutex_t *)&args->mutex_msg_received; /* mutex per accedere al buffer contenente i messaggi ricevuti */
    pthread_cond_t *cond_msg_received = (pthread_cond_t *)&args->cond_msg_received;     /* coondition variable per accedere al buffer contenente i messaggi ricevuti */
    bool closed_session = false;

    /* fin tanto che non viene chiusa la connessione o non c'è errore, controllo se ci sono eventuali nuovi messaggi */
    while (!closed_session)
    {
        // printf("THREAD READ [%s]\n", username); /* DEBUG */

        if (pthread_mutex_lock(mutex_msg_received) != 0)
        {
            fprintf(stderr, "Error: handler_read() -> pthread_mutex_lock()\n");
        }

        int rdmsg = 0;
        while ((rdmsg = read_message_from_thread_queue(*thread_index)) == -1) /* ritorna -1 in caso di buffer vuoto */
        {
            // printf("rdmsg = %d\n", rdmsg); /* DEBUG */
            pthread_cond_wait(cond_msg_received, mutex_msg_received); /* si sblocca tramite la broadcast dell'handler_connection del mittente */
        }

        /* controllo se la connessione è caduta o c'è stato un errore */
        if (rdmsg == -2)
        {
            fprintf(stderr, "Error: handler_read() -> read_message_from_thread_queue() error or connection resetted by peer\n"); /* DEBUG */
            closed_session = true;
            continue;
        }

        if (pthread_mutex_unlock(mutex_msg_received) != 0)
        {
            fprintf(stderr, "Error: handler_read() -> pthread_mutex_unlock()\n");
        }

        if (pthread_cond_broadcast(cond_msg_received) != 0)
        {
            fprintf(stderr, "Error: handler_read() -> pthread_cond_broadcast()\n");
        }

    } //fine while sessione

    if (close_connection_thread(*thread_index) != 0)
    {
        printf("errore nella chiusura della connessione ->  handler_read() thread_index#%ld\n", *thread_index);
    }
    pthread_exit(NULL);
}

/*
    Questa funzione si occupa di gestire la connessione di uno specifico utente.
*/
void *handler_connection(void *threadarg)
{
    /* ottengo gli argomenti passati come parametro */
    thread_args_t *args = (thread_args_t *)threadarg;

    size_t *thread_index = (size_t *)&args->thread_index;
    (void)thread_index; /* evita warning */
    // bool *busy = (bool *)&args->busy;                                                   /* flag per riusare le celle degli array solo se non più occupati a fare qualcosa */
    int *socket = (int *)&args->socket;         /* socket da gestire */
    char *username = (char *)&args->username;   /* username dell'utente gestito, copiato dal processo padre nel buffer del thread */
    char *IP_client = (char *)&args->IP_client; /* buffer contenente l'indirizzo ip del client */
    // char *msg_received = (char *)&args->msg_received; /* buffer contenente il messaggio ricevuto da altri client da mostrare all'utente */
    // (void)msg_received;                               /* evita warning */
    // pthread_mutex_t *mutex_msg_received = (pthread_mutex_t *)&args->mutex_msg_received; /* mutex per accedere al buffer contenente i messaggi ricevuti */
    // pthread_cond_t *cond_msg_received = (pthread_cond_t *)&args->cond_msg_received;     /* coondition variable per accedere al buffer contenente i messaggi ricevuti */
    bool closed_session = false; /* flag per gestire il caso di connessione terminata con il client */
    char receiver[BUFSIZE];      /* username del destinatario */
    char msg_to_send[BUFSIZE];   /* messaggio da inviare */
    ssize_t thread_receiver = 0; /* thread dell'utente destinatario del messaggio */
    // int err = 0;

    /* stampo le info sul client connesso */
    printf("%s:%s connected\n", IP_client, username);

    while (!closed_session)
    {
        // printf("inizio while msg %p receiver %p\n",msg_to_send,receiver);
        ssize_t byte_read = 0;
        /* leggo il destinatario del messaggio */

        byte_read = sread(*socket, receiver);
        if (byte_read < 0)
        {
            fprintf(stderr, "Errore nella lettura del destinatario.\n"); /* DEBUG */
            closed_session = true;
            continue;
        }
        else if (byte_read == 0)
        {
            printf("_connection closed by client_\n"); /* DEBUG */
            closed_session = true;
            continue;
        }

        printf("destinatario: [%s] | byte_read: %ld\n", receiver, byte_read); /* DEBUG */
        /* leggo il messaggio */

        byte_read = sread(*socket, msg_to_send);
        if (byte_read < 0)
        {
            fprintf(stderr, "Errore nella lettura del messaggio.\n"); /* DEBUG */
            closed_session = true;
            continue;
        }
        else if (byte_read == 0)
        {
            printf("_connection closed by client_\n"); /* DEBUG */
            closed_session = true;
            continue;
        }

        // printf("msg_to_send: %s\n | byte_read: %ld", msg_to_send, byte_read); /* DEBUG */

        /* cerco il thread a cui inviare il messaggio */
        printf("handler_connection() -> receiver %s\n", receiver);
        thread_receiver = find_thread_user(receiver, thread_arg_array, SOMAXCONN);
        printf("handler_connection() -> thread_receiver: %ld\n", thread_receiver); /* DEBUG */

        /* gestisco solo il caso in cui l'utente destinatario sia online/esiste */
        if (thread_receiver != -1)
        {
            char from_symbol = '>';            /* simbolo che indica da chi proviene il messaggio */
            char delim_symbol = ':';           /* simbolo che indica dove inizia il messaggio */
            char msg_to_thread[BUFSIZE];       /* messaggio formattatto per il thread destinatario */
                                               /* 
                        1 char per '>'                      ==> sizeof(char)
                        lunghezza_variabile per '<From>'    ==> strlen(username)
                        1 char per ':'                      ==> sizeof(char)
                        lunghezza_variabile per '<message>' ==> strlen(msg_to_send)
                        1 char per '\0'                     ==> sizeof(char)
                    */
            memset(msg_to_thread, 0, BUFSIZE); /* pulisco l'area di memoria che ospiterà il messaggio per il thread ricevente */

            if (snprintf(msg_to_thread, BUFSIZE - 1, "%c%s%c%s", from_symbol, username, delim_symbol, msg_to_send) < 0)
            {
                fprintf(stderr, "Error: handler_connection() -> send to thread receiver -> snprintf()\n"); /* DEBUG */
            }
            else
            {
                //printf("msg_to_thread:%s strlen[%ld]\n", msg_to_thread, strlen(msg_to_thread)); /* DEBUG */

                /* scrivo il messaggio nel buffer del thread destinatario */

                /* provo ad acquisire il lock sul buffer dei messaggi del thread destinatario ---> BLOCCANTE! */
                if (pthread_mutex_lock(&thread_arg_array[thread_receiver].mutex_msg_received) != 0)
                {
                    fprintf(stderr, "Error: handler_connection() -> pthread_mutex_lock()\n");
                }
                /* INIZIO SEZIONE CRITICA - SCRITTURA NEL BUFFER DEL MESSAGGIO AL DESTINATARIO */
                while (write_message_to_thread_queue(msg_to_thread, thread_receiver) < 0)
                {
                    fprintf(stderr, "Error: write_message_to_thread_queue()\n");
                    /* mi metto in attesa di inviare il messaggio */
                    pthread_cond_wait(&thread_arg_array[thread_receiver].cond_msg_received, &thread_arg_array[thread_receiver].mutex_msg_received);
                }

                /* sono uscito dal ciclo while quindi mi sono sbloccato e ho inviato il messaggio */
                printf("MESSAGGIO INVIATO AL THREAD CORRETTAMENTE \n"); /* DEBUG */

                /* FINE SEZIONE CRITICA */
                /* avviso tutti i thread in attesa di una modifica sul buffer*/
                if (pthread_mutex_unlock(&thread_arg_array[thread_receiver].mutex_msg_received) != 0)
                {
                    fprintf(stderr, "Error: handler_connection() -> pthread_mutex_unlock()\n");
                }
                if (pthread_cond_broadcast(&thread_arg_array[thread_receiver].cond_msg_received) != 0)
                {
                    fprintf(stderr, "Error: handler_connection() -> pthread_cond_broadcast()\n");
                }
            } //fine else errore con la snprintf

        } //fine if thread_receiver != -1

        // printf("username: [%s] | receiver: [%s] | msg_to_send: [%s]\n", username, receiver, msg_to_send); /* DEBUG */

    } //fine while sessione

    if (close_connection_thread(*thread_index) != 0)
    {
        printf("errore nella chiusura della connessione ->  handler_connection() thread_index#%ld\n", *thread_index);
    }

    pthread_exit(NULL);
}

void handler(int signo)
{
    int status;

    (void)signo; /* per evitare warning */

    /* eseguo wait non bloccanti finché ho dei figli terminati */
    while (waitpid(-1, &status, WNOHANG) > 0)
        continue;
}

/*
    Funzione per il debug.
*/
int showType(pthread_mutexattr_t *mta)
{
    int type;

    printf("Check type attribute\n");
    pthread_mutexattr_gettype(mta, &type);

    printf("The type attributed is: ");
    switch (type)
    {
    case PTHREAD_MUTEX_NORMAL:
        printf("PTHREAD_MUTEX_NORMAL (DEFAULT)\n");
        break;
    case PTHREAD_MUTEX_RECURSIVE:
        printf("PTHREAD_MUTEX_RECURSIVE\n");
        break;
    case PTHREAD_MUTEX_ERRORCHECK:
        printf("PTHREAD_MUTEX_ERRORCHECK\n");
        break;
    default:
        printf("! type Error type=%d !\n", type);
        exit(1);
    }
    return type;
}

int main(int argc, char const *argv[])
{
    /* variabili per la gestione dei socket */
    int flag_so_reuse = 1; //abilita il flag SO_REUSEADDR
    int init_socket, connected_socket;
    // struct addrinfo hints;
    // struct addrinfo *res;
    // struct sigaction sa;
    struct sockaddr_in addr_a; /* AF_INET + porta 16 bit + IP 32 bit */

    /* informazioni del client */
    struct sockaddr_in info_client; /* IP e porta del client */
    socklen_t len;
    /* - - - - - - - - - - - - */

    uint16_t PORT; /* parametro passato dall'utente */

    /* Controllo argomenti */
    if (argc != 2)
    {
        fprintf(stderr, "Errore, Uso: %s <portID>\n", argv[0]);
        exit(EXIT_FAILURE);
    }
    else
    {
        PORT = atoi(argv[1]);
    }

    // sigemptyset(&sa.sa_mask);
    // /* uso SA_RESTART per evitare di dover controllare esplicitamente se
    //  * accept è stata interrotta da un segnale e in tal caso rilanciarla
    //  * (si veda il paragrafo 21.5 del testo M. Kerrisk, "The Linux
    //  * Programming Interface") */
    // sa.sa_flags   = SA_RESTART;
    // sa.sa_handler = handler;

    // if (sigaction(SIGCHLD, &sa, NULL) == -1) {
    //         perror("sigaction");
    //         exit(EXIT_FAILURE);
    // }

    /* resetto lo spazio di memoria che ospiterà le struct dei thread */
    memset(threads, 0, sizeof(threads));

    /* resetto lo spazio di memoria che ospiterà le struct dei thread in lettura */
    memset(reading_threads, 0, sizeof(reading_threads));

    /* resetto lo spazio di memoria che ospiterà gli argomenti dei thread */
    memset(thread_arg_array, 0, sizeof(thread_arg_array));

    /* faccio il reset al valore di default della struct */
    pthread_attr_init(&attr);

    /* rendo i thread futuri creati con questi attributi joinable */
    if (pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE) != 0)
    {
        perror("pthread_attr_setdetachstate()");
        exit(EXIT_FAILURE);
    }

    /* configuro ogni thread con un id univoco che sarà riutilizzato per connessioni multiple 
       ovvero ad ogni cella dell'array viene associato un id univoco fin dall'inizio.
       Inoltre configuro tutti i thread come non occupati.
    */
    for (size_t t = 0; t < SOMAXCONN; t++)
    {

        thread_arg_array[t].thread_index = t;
        thread_arg_array[t].busy = false;
    }

    /* configuro gli attributi dei mutex */
    if (pthread_mutexattr_init(&attr_mutex) != 0)
    {
        perror("pthread_mutexattr_init()");
        exit(EXIT_FAILURE);
    }
    if ((err_thread = pthread_mutexattr_settype(&attr_mutex, PTHREAD_MUTEX_ERRORCHECK)) != 0)
    {
        errno = err_thread;
        perror("pthread_mutexattr_settype()");
        exit(EXIT_FAILURE);
    }

    showType(&attr_mutex); /* DEBUG */
    /* - - - - - - - - - - - - - - - - - - - - - - - */

    /* azzero la struttura che deve ospitare le info relative a numero di porta e indirizzo IP */
    memset(&addr_a, 0, sizeof(addr_a));

    /* configuro la famiglia di indirizzo nella struct */
    addr_a.sin_family = AF_INET; /* indirizzo IPv4 */

    /* configuro la porta nella struct con il formato di rete */
    addr_a.sin_port = htons(PORT);

    /* configuro l'indirizzo IP in modo automatico */
    addr_a.sin_addr.s_addr = htonl(INADDR_ANY); /* il sistema in automatico configura l'IP */

    /* creo il socket */
    if ((init_socket = socket(PF_INET, SOCK_STREAM, 0)) < 0) /* protocolli internet IPv4 + socket TCP + protocollo di default del SO */
    {
        perror("socket()");
        exit(EXIT_FAILURE);
    }

    /* abilito il flag SO_REUSEADDR per la socket */
    if (setsockopt(init_socket, SOL_SOCKET, SO_REUSEADDR, &flag_so_reuse, sizeof(flag_so_reuse)))
    {
        perror("setsockopt()");
        exit(EXIT_FAILURE);
    }

    /* associo IP e porta al socket */
    if ((bind(init_socket, (struct sockaddr *)&addr_a, sizeof(addr_a))) < 0)
    {
        perror("bind()");
        exit(EXIT_FAILURE);
    }

    /* metto il socket in attesa di eventuali connessioni */
    if ((listen(init_socket, SOMAXCONN)) < 0)
    {
        perror("listen()");
        exit(EXIT_FAILURE);
    }

    // unsigned int counter_iteration = 0; /* DEBUG */
    while (true)
    {

        // printf("[+] SERVER ITERATION %d\n", ++counter_iteration); /* DEBUG */
        char username[BUFSIZE];          /* buffer contenente lo username ricevuto dal client */
        char IP_client[INET_ADDRSTRLEN]; /* buffer contenente l'indirizzo ip del client */
        struct in_addr ip_addr_network;  /* contiene l'IP del client nel formato di rete */

        len = (socklen_t)sizeof(info_client);
        connected_socket = accept(init_socket, (struct sockaddr *)&info_client, &len);
        if (connected_socket < 0)
        {
            if (errno == EINTR)
                continue;
            perror("accept()");
        }
        else /* eseguo questo ramo solo se non ci sono stati errori con il connected_socket */
        {
            size_t available_thread = find_available_thread(SOMAXCONN);
            // printf("available_thread %ld\n", available_thread); /*DEBUG*/
            if (available_thread != -1) /* c'è un nuovo thread disponibile */
            {
                /* 
                    leggo lo username dalla socket, essendo di lunghezza finita, si poteva anche leggere 
                    usando la classica read
                */
                ssize_t byte_read = 0;

                memset(username, 0, BUFSIZE);

                if ((byte_read = sread(connected_socket, username)) < 0)
                {
                    fprintf(stderr, "Errore nella lettura dello username.\n");
                    continue;
                }

                // printf("main() -> sread username -> [%s] | byte_read %ld\n", username, byte_read); /* DEBUG */

                /* inizializzo gli argomenti per il nuovo thread da creare */
                thread_arg_array[available_thread].busy = true; /* la cella corrispondente al thread che stiamo creando è occupata */
                thread_arg_array[available_thread].thread_index = available_thread;
                /* 
                    Non ho usato i mutex come suggerito dall'hint della specifica in quanto
                    username e IP vengono settati dal processo principale prima di creare ogni thread
                    e sono univocamente ottenuti dal socket creato e assegnati a variabili diverse pertanto
                    non c'è il problema di dati non ricevuti in manieta atomica dai thread.
                 */

                // printf("username : [%s]\n", username); /* DEBUG */
                strcpy(thread_arg_array[available_thread].username, username);

                ip_addr_network = info_client.sin_addr; /* estraggo l'indirizzo ip */
                /* converto l'IP del client in un formato leggibile */
                if (inet_ntop(AF_INET, (void *)&ip_addr_network, IP_client, INET_ADDRSTRLEN) == NULL)
                {
                    perror("inet_ntop()");
                    exit(EXIT_FAILURE);
                }
                strncpy(thread_arg_array[available_thread].IP_client, IP_client, INET_ADDRSTRLEN);
                thread_arg_array[available_thread].socket = connected_socket;
                /* pulisco il buffer per i messaggi ricevuti da ogni utente e setto il flag di buffer pieno a false */
                memset(thread_arg_array[available_thread].msg_received, 0, BUFSIZE);
                thread_arg_array[available_thread].msg_received_full = false;
                /* inizializzo il mutex e la condition variable */
                pthread_mutex_init(&thread_arg_array[available_thread].mutex_msg_received, &attr_mutex);
                pthread_cond_init(&thread_arg_array[available_thread].cond_msg_received, NULL);

                /* una volta configurati i parametri da passargli, creo il thread di sola lettura del buffer */
                if ((err_thread = pthread_create(&reading_threads[available_thread], &attr, handler_read, (void *)&thread_arg_array[available_thread])) != 0)
                {
                    fprintf(stderr, "ERROR: return code from pthread_create() is %d\n", err_thread);
                    info_thread(reading_threads[available_thread], thread_arg_array[available_thread]);
                    continue;
                }

                /* una volta configurati i parametri da passargli, creo il thread per gestire la connessione */
                if ((err_thread = pthread_create(&threads[available_thread], &attr, handler_connection, (void *)&thread_arg_array[available_thread])) != 0)
                {
                    fprintf(stderr, "ERROR: return code from pthread_create() is %d\n", err_thread);
                    info_thread(threads[available_thread], thread_arg_array[available_thread]);
                    continue;
                }

                /* distruggo lo spazio usato per gli attributi dei thread */
                pthread_attr_destroy(&attr);
                /* distruggo lo spazio usato per gli attributi dei mutex */
                pthread_mutexattr_destroy(&attr_mutex);

                /* stacca i thread così da poter servire altre richieste */
                // printf("username: [%s] | available_thread %ld\n", username, available_thread);
                err_thread = pthread_detach(threads[available_thread]);
                if (err_thread)
                {
                    fprintf(stderr, "ERROR: return code from pthread_detach() is %d\n", err_thread);
                    info_thread(threads[available_thread], thread_arg_array[available_thread]);

                    close(connected_socket);
                }

                err_thread = pthread_detach(reading_threads[available_thread]);
                if (err_thread)
                {
                    fprintf(stderr, "ERROR: return code from pthread_detach() is %d\n", err_thread);
                    info_thread(reading_threads[available_thread], thread_arg_array[available_thread]);

                    close(connected_socket);
                }

                // printf("prima dell'exit per thread[%ld] --> %ld\n", available_thread, threads[available_thread]);
                // printf("available_thread %ld\n", available_thread); /* DEBUG */
                // printf("dopo dell'exit per thread[%ld] --> %ld\n", available_thread, threads[available_thread]);
            }
        }
    }

    pthread_exit(NULL); /* finally, just exit w/o return value */
    /* in caso... */
    close(init_socket);

    return 0;
}
