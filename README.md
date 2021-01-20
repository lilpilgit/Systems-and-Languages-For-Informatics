# Systems-and-Languages-For-Informatics
Repository containing the projects of Prof. Kocian and Prof. Ferrari for the exam of `Systems and Languages for Informatics` of the Cybersecurity LM-66 Faculty ( University of Pisa)

Information about the methods of execution of the didactic interpreter in Ocaml are illustrated in the [report](https://github.com/lilpilgit/Systems-and-Languages-For-Informatics/tree/main/Ferrari/RELAZIONE)

To compile multithreaded client-server chat in C, gcc-9.3.0 was used.
```
gcc-9 -Wall -g -pthread server.c -o server
gcc-9 -Wall -g -pthread client.c -o client
```

To run the server:
```./server <port>```
To run the clients:
```./client <ip_server> <username> <port_server>```
