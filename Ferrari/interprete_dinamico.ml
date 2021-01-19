exception DynamicTypeError of string (* eccezione per errore di tipo a run time *)
exception SetIsEmpty of string (* eccezione per insieme vuoto a run time *)


type ide = string;;

(* tipi ammessi nel linguaggio *)
type ttype = 
    | IntType
    | StringType
    | BoolType
    | FunType of ttype * ttype
    | SetType of ttype;;

(* albero di sintassi astratta del linguaggio *)
type expr =
    | CstTrue (* corrisponde al letterale true *)
    | CstFalse (* corrisponde al letterale false *)
    | CstInt of int (* corrisponde al letterale costruttore che trasporta un intero *)
    | CstString of string (* corrisponde al letterale costruttore che trasporta una stringa *)
    | EqualsString of expr * expr (* corrisponde all'uguaglianza tra stringhe *)
    | Den of ide (* corrisponde all'identificatore di variabile *)
    | Add of expr * expr (* corrisponde alla somma tra interi *)
    | Sub of expr * expr (* corrisponde alla differenza tra interi *)
    | Times of expr * expr (* corrisponde al prodotto tra interi *)
    | IsZero of expr (* corrisponde a verificare se un intero ha valore 0 *)
    | Equals of expr * expr (* corrisponde a verificare l'uguaglianza tra 2 espressioni intere *)
    | And of expr * expr (* corrisponde all'and tra due espressioni *)
    | Or of expr * expr (* corrisponde all'or tra due espressioni *)
    | Not of expr (* corrisponde alla negazione di un espressione *)
    | IfThenElse of expr * expr * expr (* corrisponde alla valutazione di un if then else *)
    | Let of ide * expr * expr (* corrisponde alla introduzione di una nuova variabile *)
    (* sia in Fun che FunRec l'argomento verrà passato tramite la Apply, che invece corrisponde alla applicazione di funzione *)
    | Fun of ide * expr * ttype * ttype (* corrisponde alla introduzione di una funzione: nome argomento, corpo, tipo argomento, tipo del ritorno *)
    | FunRec of ide * ide * ttype * ttype * expr * expr (* corrisponde alla introduzione ricorsiva di funzioni *)
    | Apply of expr * expr (* applicazione di una funzione *)
    (* Costruttori dell'insieme *)
    | EmptySet of ttype (* costruttore di un insieme vuoto di tipo `ttype` *)
    | Singleton of ttype * expr (* costruttore di un insieme costituito da un solo elemento `expr` del tipo `ttype` *)
    | Of of ttype * set_expr (* costruttore di un insieme di tipo `ttype` a partire da una lista di espressioni `set_expr` *)
    (* Operazioni di base *)
    | Union of expr * expr (* unione di due insiemi *)
    | Intersection of expr * expr (* intersezione di due insiemi *)
    | Difference of expr * expr (* differenza tra due insiemi *)
    (* Operazioni aggiuntive *)
    | Insert of expr * expr (* inserisce un elemento in un insieme *)
    | Remove of expr * expr (* rimuove un elemento da un insieme *)
    | Contains of expr * expr (* verifica se un insieme contiene un elemento *)
    | Subset of expr * expr (* verifica se un insieme è sottoinsieme di un altro insieme *)
    | IsEmpty of expr (* verifica se un insieme è vuoto *)
    | MinOf of expr (* trova l'elemento minimo nell'insieme *)
    | MaxOf of expr (* trova l'elemento massimo in un insieme *)
    (* Operatori funzionali *)
    | ForAll of expr * expr (* controlla se tutti gli elementi dell'insieme soddisfano il predicato *)
    | Exists of expr * expr (* controlla se esiste almeno un elemento dell'insieme che soddisfa la proprietà del predicato *)
    | Filter of expr * expr (* restituisce l'insieme degli elementi appartenenti all'insieme che soddisfano un predicato *)
    | Map of expr * expr (* restituisce l'insieme dei valori v tali che v = function(x) con x appartenente all'insieme *)
    and set_expr = 
        | Empty (* insieme vuoto *)
        | Cons of expr * set_expr;; (* oppure è il cons di un espressione e del resto dell'insieme *)
    
(* ambiente polimorfico *)
type 'v env = (string * 'v) list;;

(* valori a runtime *)
type evT = 
    | Int of int
    | String of string
    | Bool of bool 
    | Closure of ide * expr * evT env * ttype * ttype 
    (* ide: nome del parametro formale, expr: codice della funzione, evT env ambiente al momento della dichiarazione,
       ttype x2 : tipo in ingresso e in uscita della funzione *)
    
    (* introduco la RecClosure per la gestione della ricorsione *)
    | RecClosure of ide * ide * expr * evT env * ttype * ttype 
    (* ide: nome della funzione, ide: nome del parametro formale, expr: codice della funzione, evT env ambiente al momento della dichiarazione,
       ttype x2 : tipo in ingresso e in uscita della funzione *)
    | Set of ttype  * set_val (* il costruttore di Set prende un tipo del linguaggio e un valore dell'insieme *)
    | Unbound
    and set_val = 
        | EmptyV 
        | ConsV of evT * set_val;;

let empty_env : evT env  = [] ;;

let bind (env: evT env) (i: ide) (v: evT) = ( i, v ) :: env;;

let rec lookup (env: evT env) (i: ide) : evT = 
    match env with
    | [] ->  Unbound
    | (a,v)::_ when a = i -> v
    | _::e -> lookup e i;;

(*  type checking dinamico 
    typecheck ha tipo string -> evT -> bool, infatti ritorna bool
*)
let rec typecheck (t:string) (v : evT) : bool = 
match t with
    | "int" -> (match v with (* controllo se il valore passato è di tipo int *)
                | Int _ -> true
                | _ -> false )
    | "string" -> (match v with (* controllo se il valore passato è di tipo string *)
                | String _ -> true
                | _ -> false )
    | "bool" -> (match v with (* controllo se il valore passato è di tipo bool *)
                | Bool _ -> true
                | _ -> false )
    | "fun" -> (match v with   (* controllo se il valore passato è di tipo funval *)
                | Closure _ -> true
                | RecClosure _ -> true
                | _ -> false )
    | "set" -> (match v with   (* controllo se il valore passato è di tipo set *)
                | Set _ -> true
                | _ -> false )
    | _ -> failwith "Typechecking dinamico fallito: la stringa non è corretta";;

    
(* gli passo uno dei tipi consentiti dal linguaggio e ritorna una funzione evt -> bool, sto facendo uso del currying 
   questa è una funzione ausiliaria che consente di effettuare una chiamata parametrizzata al typechecker dinamico sulla
   base del tipo passato come parametro *)
let check_from_lang_ttype (tt: ttype) : evT -> bool = 
match tt with
    | IntType       -> typecheck "int"
    | StringType    -> typecheck "string"
    | BoolType      -> typecheck "bool"
    | FunType(_,_)       -> typecheck "fun"
    | SetType(_)       -> typecheck "set";;


(* funzioni ausiliarie *)
let int_add (n: evT) (m: evT) (*: evT *) =
    match typecheck "int" n, typecheck "int" m, n, m with
    | true, true, Int a, Int b -> Int(a + b)
    | _, _, _, _                  -> raise(DynamicTypeError "Add può essere chiamata solo su interi");;

let int_sub(n: evT) (m: evT) : evT = 
    match typecheck "int" n, typecheck "int" m, n, m with
    | true, true, Int a, Int b -> Int(a - b)
    | _,_,_,_                  -> raise(DynamicTypeError "Sub può essere chiamata solo su interi");;

let int_times(n: evT) (m: evT) : evT = 
    match typecheck "int" n, typecheck "int" m, n, m with
    | true, true, Int a, Int b -> Int (a * b)
    | _,_,_,_                  -> raise(DynamicTypeError "Times può essere chiamata solo su interi");;

let is_zero(n: evT) : evT = 
    match typecheck "int" n, n with
    | true, Int a -> Bool (a = 0)
    | _,_ -> raise(DynamicTypeError "IsZero può essere chiamata solo su interi");;

let int_equals(n: evT) (m: evT) : evT = 
    match typecheck "int" n, typecheck "int" m, n, m with
    | true, true, Int a, Int b -> Bool (a = b)
    | _,_,_,_                  -> raise(DynamicTypeError "Equals può essere chiamata solo su interi");;

let bool_and(n: evT) (m: evT) : evT = 
    match typecheck "bool" n, typecheck "bool" m, n, m with
    | true, true, Bool a, Bool b -> Bool (a && b)
    | _,_,_,_                  -> raise(DynamicTypeError "And può essere chiamata solo su booleani");;

let bool_or(n: evT) (m: evT) : evT = 
    match typecheck "bool" n, typecheck "bool" m, n, m with
    | true, true, Bool a, Bool b -> Bool (a || b)
    | _,_,_,_                  -> raise(DynamicTypeError "Or può essere chiamata solo su booleani");;

let bool_not(n: evT) : evT = 
    match typecheck "bool" n, n with
    | true, Bool a -> Bool (not a)
    | _,_                -> raise(DynamicTypeError "Not può essere chiamata solo su booleani");;

let string_equals(s: evT) (z: evT) : evT = 
    match typecheck "string" s, typecheck "string" z, s, z with
    | true, true, String a, String b -> Bool (a = b)
    | _,_,_,_                  -> raise(DynamicTypeError "EqualsString può essere chiamata solo su stringhe");;

let rec set_contains (s: set_val) (v: evT) : bool = 
    match s with
    | EmptyV -> false
    | ConsV (v', _) when v' = v -> true
    | ConsV (_,s') -> set_contains s' v;;

let rec set_union (s1: set_val) (s2: set_val) : set_val =
    match s1 with
    | EmptyV -> s2 (* se l'insieme s1 è vuoto ritorno s2 *)
    | ConsV (v1, s1') ->
                        if set_contains s2 v1 (* se l'insieme s2 contiene il valore in testa al cons *)
                        then set_union s1' s2 (* unisco solo la parte rimanente di s1 in quanto sto facendo l'unione *)
                        else set_union s1' (ConsV(v1,s2));; (* se l'insieme s2 non contiene il valore v1 allora lo aggiungo *)

let rec set_intersection (s1: set_val) (s2: set_val) : set_val = 
    match s1 with
    | EmptyV -> EmptyV
    | ConsV (v1,s1') ->
                        if set_contains s2 v1 (* se l'insieme s2 contiene il valore v1 allora ... *)
                        then ConsV(v1, (set_intersection s1' s2)) (* ritorno un insieme fatto da v1 e la chiamata ricorsiva, in quanto l'intersezione prende i valori comuni *)
                        else set_intersection s1' s2;; (* se il valore v1 non è comune ai 2 insiemi allora lo scarto *)

let rec set_difference (s1: set_val) (s2: set_val) : set_val = 
    match s1 with
    | EmptyV -> EmptyV
    | ConsV (v1,s1') ->
                        if set_contains s2 v1 (* se l'insieme s2 contiene il valore v1 allora ... *)
                        then set_difference s1' s2 (* scarto il valore v1 e continuo facendo una chiamata ricorsiva *)
                        else ConsV(v1, (set_difference s1' s2));; (* se il valore v1 non è in s2 allora lo mantengo *)

let rec set_remove (s: set_val) (v: evT) : set_val = 
    match s with
    | EmptyV -> EmptyV
    | ConsV (v',s') when v' = v -> s' (* ho trovato l'elemento che volevo rimuovere *)
    | ConsV (v',s') -> ConsV(v', set_remove s' v);; (* l'elemento v' non è quello che voglio rimuovere dunque lo mantengo *)

let rec set_subset (s1: set_val) (s2: set_val) : bool = 
    match s1 with
    | EmptyV -> true (* un insieme vuoto è sempre sottoinsieme di qualsiasi altro insieme *)
    | ConsV (v', s') ->
                        if set_contains s2 v' (* se l'insieme s2 contiene il valore v' ... *)
                        then set_subset s' s2 (* proseguo chiamando ricorsivamente la set_subset, in questo modo anche se i valori
                                              non sono ordinati, comunque viene individuato il subset *)
                        else false;;

let rec set_max (s: set_val) : evT =
    match s with 
    | EmptyV -> raise(SetIsEmpty "Impossibile trovare il massimo su un insieme vuoto")
    | ConsV (v, EmptyV) -> v (* se si tratta di un singleton allora il minimo è solamente quell elemento contenuto *)
    | ConsV (v, s') ->
                        match set_max s', v with
                        | Int a, Int b -> Int (max a b) (* uso la max di ocaml *)
                        | String a, String b -> String (max a b)
                        | Bool a, Bool b -> Bool (max a b)
                        | _, _ -> raise(DynamicTypeError "Impossibile calcolare il massimo su un tipo diverso da Int, String o Bool");;

let rec set_min (s: set_val) : evT = 
    match s with 
    | EmptyV -> raise(SetIsEmpty "Impossibile trovare il minimo su un insieme vuoto")
    | ConsV (v, EmptyV) -> v (* se si tratta di un singleton allora il minimo è solamente quell elemento contenuto *)
    | ConsV (v, s') ->
                        match set_min s', v with
                        | Int a, Int b -> Int (min a b) (* uso la min di ocaml *)
                        | String a, String b -> String (min a b)
                        | Bool a, Bool b -> Bool (min a b)
                        | _, _ -> raise(DynamicTypeError "Impossibile calcolare il minimo su un tipo diverso da Int, String o Bool");;

(* interprete *)
let rec eval (e: expr) (env: evT env) : evT = 
    match e with
    | CstInt n -> Int n
    | CstTrue -> Bool true
    | CstFalse -> Bool false
    | CstString s -> String s
    | EqualsString (s, z) -> string_equals (eval s env) (eval z env) (* corrisponde all'uguaglianza tra stringhe *)
    | Den i -> lookup env i (* effettuo un lookup nell'ambiente env per l'identificatore i *)
    | Add (e1, e2) -> int_add (eval e1 env) (eval e2 env)(* corrisponde alla somma tra interi *)
    | Sub (e1, e2) -> int_sub (eval e1 env) (eval e2 env) (* corrisponde alla differenza tra interi *)
    | Times (e1, e2) -> int_times (eval e1 env) (eval e2 env) (* corrisponde al prodotto tra interi *)
    | IsZero e -> is_zero (eval e env)(* corrisponde a verificare se un intero ha valore 0 *)
    | Equals (e1, e2) -> int_equals (eval e1 env) (eval e2 env) (* corrisponde a verificare l'uguaglianza tra 2 espressioni intere *)
    | And (e1, e2) -> bool_and (eval e1 env) (eval e2 env) (* corrisponde all'and tra due espressioni *)
    | Or (e1, e2) -> bool_or (eval e1 env) (eval e2 env) (* corrisponde all'or tra due espressioni *)
    | Not e -> bool_not (eval e env) (* corrisponde alla negazione di un espressione *)
    | IfThenElse (guardia, e1, e2) -> (* corrisponde alla valutazione di un if then else *)
                                    (
                                        let evalCond = eval guardia env in (* valuto l'espressione della guardia... *)
                                            match typecheck "bool" evalCond, evalCond with (* prima valuto che la guardia sia di tipo bool... *)
                                            | true, Bool true -> eval e1 env (* se la guardia è booleana e il valore del ramo if è true, valuto il ramo if *)
                                            | true, Bool false -> eval e2 env (* se la guardia è booleana e il valore del ramo if è false, valuto il ramo else *)
                                            | _,_ -> raise (DynamicTypeError "La guardia dell' ifthenelse deve essere di tipo booleano") 
                                    )
    | Let (i, e1, e2) -> eval e2 (bind env i (eval e1 env))(* corrisponde alla introduzione di una nuova variabile *)
    | Fun (i, body, t1, t2) -> Closure (i, body, env, t1, t2) (* corrisponde alla introduzione di una funzione: nome argomento, corpo, tipo argomento, tipo del ritorno *)
    | FunRec (funIde, p, t1, t2, bodyFun, bodyLet) ->  (* corrisponde alla introduzione ricorsiva di funzioni *)
                                                    let recClosure = RecClosure (funIde, p, bodyFun, env, t1, t2) in 
                                                    let bindEnv = bind env funIde recClosure in
                                                    eval bodyLet bindEnv
    | Apply (funct, arg) ->  (* applicazione di una funzione *)
                            let funClosure = eval funct env in (* valuto la funzione nell'ambiente e vedo se è una closure o recursive closure... *)
                            (match funClosure with 
                            | Closure (param, bodyFun, declEnvFun, t1, _) -> 
                                let actualVal = eval arg env in (* valuto il parametro ottenendo il valore attuale *)
                                if check_from_lang_ttype t1 actualVal = true
                                then (
                                        let actualEnv = bind declEnvFun param actualVal in
                                        eval bodyFun actualEnv (* valuto il body della funzione chiamata all'interno dell'ambiente di dichiarazione della
                                                                  funzione, con l'aggiunta del binding tra il parametro passato e il valore attuale calcolato *)
                                )
                                else raise (DynamicTypeError "Apply: ha fallito perchè il tipo del parametro attuale è errato")
                            | RecClosure (idFun, param, bodyFun, declEnvFun, t1, _) -> 
                                let actualVal = eval arg env in (* valuto il parametro ottenendo il valore attuale *)
                                if check_from_lang_ttype t1 actualVal = true
                                then (
                                        let recEnv = bind declEnvFun idFun funClosure in 
                                (* l'ambiente ricorsivo è creato facendo il legame nell'ambiente al momento della dichiarazione della funzione 
                                   con il nome f e il suo valore. Quindi ci ricordiamo nell'ambiente di definizione che f è stata dichiarata
                                   esattamente in quell'ambiente ed è una funzione ricorsiva. Per una funzione ricorsiva infatti, nella closure
                                   il puntatore all'ambiente punta esattamente all'ambiente in cui questa è stata definita *)
                                        let actualEnv = bind recEnv param actualVal in (* ambiente di valutazione della funzione *)
                                        eval bodyFun actualEnv
                                )
                                else raise (DynamicTypeError "Apply: ha fallito perchè il tipo del parametro attuale è errato")
                            | _ -> raise (DynamicTypeError "Apply: ha fallito perchè il primo argomento non è una funzione")
                            )                                
    (* Costruttori dell'insieme *)
    | EmptySet t -> Set(t, EmptyV) (* costruttore di un insieme vuoto di tipo `ttype` *)
    | Singleton (t, expr) -> (* costruttore di un insieme costituito da un solo elemento `expr` del tipo `ttype` *)
                            let v = eval expr env in (* valuto l'espressione costituente l'insieme nell'ambiente *)
                            if check_from_lang_ttype t v
                            then Set(t, ConsV(v,EmptyV))
                            else raise (DynamicTypeError "Il tipo del singleton non corrisponde con quello del valore")      
    | Of (t, expr_list) -> (* costruttore di un insieme di tipo `ttype` a partire da una lista di espressioni (un cons di espressioni o un espressione vuota) `set_expr` *)
                    let set_v = set_eval expr_list t env in (* valuto la lista delle espressioni passate per trasformarla in una lista di valori dell'insieme *)
                                                        (* viene fatto anche il controllo dei tipi, grazie al t passato come parametro *)
                    Set(t, set_v)
    (* Operazioni di base *)
    | Union (set_e1, set_e2) -> (* unione di due insiemi *)
                        (
                            match eval set_e1 env, eval set_e2 env with
                            | Set(t1, set_v1), Set(t2, set_v2) when t1 = t2 -> (* se i tipi dei 2 insiemi combaciano posso unirli *)
                                                                                Set(t1, set_union set_v1 set_v2) (* ritorno un set di tipo t1=t2 e l'unione dei valori *)
                            | _, _ -> raise(DynamicTypeError "I tipi degli insiemi che si vogliono unire non combaciano")                            
                        )
    | Intersection (set_e1, set_e2) -> (* intersezione di due insiemi *)
                        (
                            match eval set_e1 env, eval set_e2 env with
                            | Set(t1, set_v1), Set(t2, set_v2) when t1 = t2 -> (* se i tipi dei 2 insiemi combaciano posso fare l'intersezione *)
                                                                                Set(t1, set_intersection set_v1 set_v2) (* ritorno un set di tipo t1=t2 e l'intersezione dei valori *)
                            | _, _ -> raise(DynamicTypeError "I tipi degli insiemi che si vogliono intersecare non combaciano")                            
                        ) 
    | Difference (set_e1, set_e2) -> (* differenza di due insiemi *)
                        (
                            match eval set_e1 env, eval set_e2 env with
                            | Set(t1, set_v1), Set(t2, set_v2) when t1 = t2 -> (* se i tipi dei 2 insiemi combaciano posso fare la differenza *)
                                                                                Set(t1, set_difference set_v1 set_v2) (* ritorno un set di tipo t1=t2 e la differenza dei valori *)
                            | _, _ -> raise(DynamicTypeError "I tipi degli insiemi di cui si vuole la differenza non combaciano")                            
                        )
    (* Operazioni aggiuntive *)
    | Insert (elem, set_e) -> (* inserisce un elemento in un insieme *)
                        (
                            match eval set_e env with (* valuto l'espressione che forma l'insieme... *)
                            | Set(t, set_v) ->  (* estraggo il tipo e i valori dell'insieme *)
                                                let v = eval elem env in (* valuto l'elemento da aggiungere ... *)
                                                if check_from_lang_ttype t v && not (set_contains set_v v) (* il tipo dell'insieme e dell'elemento valutato coincidono 
                                                                                                              e l'insieme valutato non contiene il valore dell'elemento ...*)
                                                then Set(t, ConsV(v, set_v)) (* aggiungo l'elemento all'insieme *)
                                                else Set(t, set_v) (* altrimenti ritorna l'insieme come prima *)
                            | _ -> raise(DynamicTypeError "Insert: ha fallito perchè non è stata chiamata su un insieme")                            
                        ) 
    | Remove (elem, set_e) -> (* rimuove un elemento in un insieme *)
                        (
                            match eval set_e env with (* valuto l'espressione che forma l'insieme... *)
                            | Set(t, set_v) ->  (* estraggo il tipo e i valori dell'insieme *)
                                                let v = eval elem env in (* valuto l'elemento da aggiungere ... *)
                                                if check_from_lang_ttype t v (* il tipo dell'insieme e dell'elemento valutato da rimuovere coincidono *)                                                               
                                                then Set(t, set_remove set_v v) (* rimuovo l'elemento dall'insieme *)
                                                else Set(t, set_v) (* altrimenti ritorna l'insieme come prima *)
                            | _ -> raise(DynamicTypeError "Remove: ha fallito perchè non è stata chiamata su un insieme")                            
                        ) 
    | Contains (elem, set_e) -> (* verifica se un insieme contiene un elemento *)
                                (
                                    match eval set_e env with
                                    | Set(t, set_v) -> (* estraggo il tipo e i valori dell'insieme... *)
                                                        let v = eval elem env in (* valuto l'argomento da aggiungere *)
                                                        if check_from_lang_ttype t v (* il tipo dell'insieme e dell'elemento valutato da verificare coincidono... *)
                                                        then Bool (set_contains set_v v)
                                                        else raise(DynamicTypeError "Contains: ha fallito perchè i tipi dell'insieme e dell'elemento non combaciano")
                                    | _ -> raise(DynamicTypeError "Contains: ha fallito perchè non è stata chiamata su un insieme")  
                                )
    | Subset (set_e1, set_e2) -> (* verifica se un insieme è sottoinsieme di un altro insieme *)
                        (
                            match eval set_e1 env, eval set_e2 env with
                            | Set(t1, set_v1), Set(t2, set_v2) ->
                                                                if t1 = t2 (* se i tipi dei 2 insiemi combaciano posso unirli *)
                                                                then Bool (set_subset set_v1 set_v2) (* ritorno un set di tipo t1=t2 e l'unione dei valori *)
                                                                else raise (DynamicTypeError "Subset: ha fallito perchè i tipi degli insiemi non combaciano")
                            | _, _ -> raise(DynamicTypeError "Subset: ha fallito perchè non è stata chiamata su due insiemi")                            
                        )
    | IsEmpty set_e -> (* verifica se un insieme è vuoto *)
                        (
                            match eval set_e env with
                            | Set(_, set_v) -> 
                                                if set_v = EmptyV
                                                then Bool true
                                                else Bool false
                            | _ -> raise(DynamicTypeError "Impossibile chiamare IsEmpty su qualcosa diverso dall'insieme")                    
                        )
    | MinOf set_e -> (* trova l'elemento minimo nell'insieme *)
                        (
                            match eval set_e env with
                            | Set(t, set_v) -> 
                                                if t = IntType || t = BoolType || t = StringType
                                                then set_min set_v
                                                else raise(DynamicTypeError "Impossibile trovare il minimo su un insieme diverso da Int, String o Bool")
                            | _ -> raise(DynamicTypeError "Impossibile chiamare MinOf su qualcosa diverso dall'insieme")                    
                        )
    | MaxOf set_e -> (* trova l'elemento massimo nell'insieme *)
                        (
                            match eval set_e env with
                            | Set(t, set_v) -> 
                                                if t = IntType || t = BoolType || t = StringType
                                                then set_max set_v
                                                else raise(DynamicTypeError "Impossibile trovare il massimo su un insieme diverso da Int, String o Bool")
                            | _ -> raise(DynamicTypeError "Impossibile chiamare MaxOf su qualcosa diverso dall'insieme")                    
                        )
    (* Operatori funzionali *)
    | ForAll (predicate, set_e) -> (* controlla se tutti gli elementi dell'insieme soddisfano il predicato *)
                                    (
                                        match eval predicate env, eval set_e env with  (* valuto il predicato e l'insieme nell'ambiente *)
                                        | RecClosure(ideFun, param, bodyFun, declEnvFun, t1, t2) as funClosure, Set(t, set_v) ->
  (* controllo che il tipo in ingresso sia uguale al tipo dell'insieme e il tipo di uscita sia un bool *)           if t1 = t && t2 = BoolType  
                                                                                                                    then set_forall funClosure set_v
                                                                                                                    else raise (DynamicTypeError "ForAll: ha fallito perchè il primo argomento deve essere una funzione con input avente stesso tipo dell'insieme e output di tipo booleano")
                                        | Closure(param, bodyFun, declEnvFun, t1, t2) as funClosure, Set(t, set_v) ->
  (* controllo che il tipo in ingresso sia uguale al tipo dell'insieme e il tipo di uscita sia un bool *)           if t1 = t && t2 = BoolType  
                                                                                                                    then set_forall funClosure set_v
                                                                                                                    else raise (DynamicTypeError "ForAll: ha fallito perchè il primo argomento deve essere una funzione con input avente stesso tipo dell'insieme e output di tipo booleano")
                                        | _ -> raise (DynamicTypeError "ForAll: ha fallito perchè deve essere chiamata con un predicato e un insieme")
                                    )
    
    | Exists (predicate, set_e) -> (* controlla se esiste almeno un elemento dell'insieme che soddisfa la proprietà del predicato *)
                                    (
                                        match eval predicate env, eval set_e env with  (* valuto il predicato e l'insieme nell'ambiente *)
                                        | RecClosure(ideFun, param, bodyFun, declEnvFun, t1, t2) as funClosure, Set(t, set_v) ->
  (* controllo che il tipo in ingresso sia uguale al tipo dell'insieme e il tipo di uscita sia un bool *)           if t1 = t && t2 = BoolType  
                                                                                                                    then set_exists funClosure set_v
                                                                                                                    else raise (DynamicTypeError "Exists: ha fallito perchè il primo argomento deve essere una funzione con input avente stesso tipo dell'insieme e output di tipo booleano") 
                                        | Closure(param, bodyFun, declEnvFun, t1, t2) as funClosure, Set(t, set_v) ->
  (* controllo che il tipo in ingresso sia uguale al tipo dell'insieme e il tipo di uscita sia un bool *)           if t1 = t && t2 = BoolType  
                                                                                                                    then set_exists funClosure set_v
                                                                                                                    else raise (DynamicTypeError "Exists: ha fallito perchè il primo argomento deve essere una funzione con input avente stesso tipo dell'insieme e output di tipo booleano")
                                        | _ -> raise (DynamicTypeError "Exists: ha fallito perchè deve essere chiamata con un predicato e un insieme")
                                    ) 
    | Filter (predicate, set_e) -> (* restituisce l'insieme degli elementi appartenenti all'insieme che soddisfano un predicato *)
                                    (
                                        match eval predicate env, eval set_e env with  (* valuto il predicato e l'insieme nell'ambiente *)
                                        | RecClosure(ideFun, param, bodyFun, declEnvFun, t1, t2) as funClosure, Set(t, set_v) ->
  (* controllo che il tipo in ingresso sia uguale al tipo dell'insieme e il tipo di uscita sia un bool *)           if t1 = t && t2 = BoolType  
                                                                                                                    then Set(t, set_filter funClosure set_v) (* creo un set a partire dal ConsV o dall'EmptyV ritornato dalla funzione ausiliaria *)
                                                                                                                    else raise (DynamicTypeError "Filter: ha fallito perchè il primo argomento deve essere una funzione con input avente stesso tipo dell'insieme e output di tipo booleano")
                                        | Closure(param, bodyFun, declEnvFun, t1, t2) as funClosure, Set(t, set_v) ->
  (* controllo che il tipo in ingresso sia uguale al tipo dell'insieme e il tipo di uscita sia un bool *)           if t1 = t && t2 = BoolType  
                                                                                                                    then Set(t, set_filter funClosure set_v) (* creo un set a partire dal ConsV o dall'EmptyV ritornato dalla funzione ausiliaria *)
                                                                                                                    else raise (DynamicTypeError "Filter: ha fallito perchè il primo argomento deve essere una funzione con input avente stesso tipo dell'insieme e output di tipo booleano")
                                        | _ -> raise (DynamicTypeError "Filter: ha fallito perchè deve essere chiamata con un predicato e un insieme")
                                    ) 
    | Map (func, set_e) -> (* restituisce l'insieme dei valori v tali che v = function(x) con x appartenente all'insieme *)
                        (
                            match eval func env, eval set_e env with  (* valuto il predicato e l'insieme nell'ambiente *)
                            | RecClosure(ideFun, param, bodyFun, declEnvFun, t1, t2) as funClosure, Set(t, set_v) ->
(* controllo che il tipo in ingresso sia uguale al tipo dell'insieme e il tipo di uscita sia un bool *) if t1 = t  
(* il tipo dell'insieme deve essere t2 ovvero il tipo ritornato dall'applicazione della funzione a ciascun valore dell'insieme *)
                                                                                                        then Set(t2, set_map funClosure set_v)
                                                                                                        else raise (DynamicTypeError "Map: ha fallito perchè il primo argomento deve essere una funzione con input avente stesso tipo dell'insieme e output di tipo booleano")
                            | Closure(param, bodyFun, declEnvFun, t1, t2) as funClosure, Set(t, set_v) ->
(* controllo che il tipo in ingresso sia uguale al tipo dell'insieme e il tipo di uscita sia un bool *) if t1 = t  
(* il tipo dell'insieme deve essere t2 ovvero il tipo ritornato dall'applicazione della funzione a ciascun valore dell'insieme *)
                                                                                                        then Set(t2, set_map funClosure set_v)
                                                                                                        else raise (DynamicTypeError "Map: ha fallito perchè il primo argomento deve essere una funzione con input avente stesso tipo dell'insieme e output di tipo booleano")
                            | _ -> raise (DynamicTypeError "Map: ha fallito perchè deve essere chiamata con una funzione e un insieme")
                        )                             

    
    (*il tipo t lo passo così da fare un controllo sul tipo prima della valutazione dell'espressione *)
    and set_eval (set_e: set_expr) (t: ttype) (env: evT env) : set_val = 
        match set_e with
        | Empty -> EmptyV (* se l'insieme è vuoto ritorna l'evaluation type dell'insieme vuoto *)
        | Cons (e, set_e') -> (* decido di valutare prima il primo valore in testa così da evitare di chiamare la set_eval sul resto dell'insieme che è molto più grande in genere *)
                            let v = eval e env in
                            if check_from_lang_ttype t v (* controllo il tipo *)
                            then
                                let set_v' = set_eval set_e' t env in (* poi valuto il resto dell'insieme *)
                                if set_contains set_v' v (* se il nuovo valore calcolato è contenuto nel resto dell'insieme calcolato *)
                                then set_v'              (*... non lo aggiunge dunque evito i duplicati! *)
                                else ConsV (v, set_v')   (*... altrimenti lo aggiunge tramite il cons *)
                            else raise(DynamicTypeError "Il tipo dell'insieme generato con of non corrisponde con quello del valore")
    
    and set_forall (closure: evT) (set_v: set_val) : evT = 
        match set_v with
        | EmptyV -> Bool true (* se l'insieme è vuoto restituisce true *)
        | ConsV (v', s') -> (* se l'insieme invece non è vuoto ... *)
                (
                    match closure with
                    | Closure (param, bodyFun, declEnvFun, _, _) ->
                                                                    let actualEnv = bind declEnvFun param v' in (* aggiungo il binding tra il parametro formale ed attuale all'ambiente *)
                                                                    (
                                                                        match eval bodyFun actualEnv with (* calcolo la funzione sul primo parametro *)
                                                                        | Bool(value) -> 
                                                                                if (not value)
                                                                                then Bool false (* se almeno un elemento non rispetta il predicato esco immediatamente con false*)
                                                                                else set_forall closure s' (* altrimenti chiamo ricorsivamente passandogli la rimanente parte dell'insieme *)
                                                                        | _ -> raise(DynamicTypeError "set_forall: la valutazione della funzione non ha ritornato un bool")
                                                                    )
                    | RecClosure (ideFun, param, bodyFun, declEnvFun, _, _) ->
                                                                    let recEnv = bind declEnvFun ideFun closure in (* aggiungo il binding tra il parametro formale ed attuale all'ambiente *)
                                                                    let actualEnv = bind recEnv param v' in
                                                                    (
                                                                        match eval bodyFun actualEnv with (* calcolo la funzione sul primo parametro *)
                                                                        | Bool(value) -> 
                                                                                if (not value)
                                                                                then Bool false (* se almeno un elemento non rispetta il predicato esco immediatamente con false*)
                                                                                else set_forall closure s' (* altrimenti chiamo ricorsivamente passandogli la rimanente parte dell'insieme *)
                                                                        | _ -> raise(DynamicTypeError "set_forall: la valutazione della funzione non ha ritornato un bool")
                                                                    )
                    | _ -> raise(DynamicTypeError "set_forall: ha fallito perchè il primo parametro deve essere una closure o rec_closure")                                                
                )
    and set_exists (closure: evT) (set_v: set_val) : evT = 
        match set_v with
        | EmptyV -> Bool false (* se l'insieme è vuoto restituisce false *)
        | ConsV (v', s') -> (* se l'insieme invece non è vuoto ... *)
                (
                    match closure with
                    | Closure (param, bodyFun, declEnvFun, _, _) ->
                                                                    let actualEnv = bind declEnvFun param v' in (* aggiungo il binding tra il parametro formale ed attuale all'ambiente *)
                                                                    (
                                                                        match eval bodyFun actualEnv with (* calcolo la funzione sul primo parametro *)
                                                                        | Bool(value) -> 
                                                                                if (value)
                                                                                then Bool true (* se almeno un elemento rispetta il predicato ritorno true*)
                                                                                else set_forall closure s' (* altrimenti chiamo ricorsivamente passandogli la rimanente parte dell'insieme *)
                                                                        | _ -> raise(DynamicTypeError "set_exists: la valutazione della funzione non ha ritornato un bool")
                                                                    )
                    | RecClosure (ideFun, param, bodyFun, declEnvFun, _, _) ->
                                                                    let recEnv = bind declEnvFun ideFun closure in (* aggiungo il binding tra il parametro formale ed attuale all'ambiente *)
                                                                    let actualEnv = bind recEnv param v' in
                                                                    (
                                                                        match eval bodyFun actualEnv with (* calcolo la funzione sul primo parametro *)
                                                                        | Bool(value) -> 
                                                                                if (value)
                                                                                then Bool true (* se almeno un elemento rispetta il predicato ritorno true*)
                                                                                else set_forall closure s' (* altrimenti chiamo ricorsivamente passandogli la rimanente parte dell'insieme *)
                                                                        | _ -> raise(DynamicTypeError "set_exists: la valutazione della funzione non ha ritornato un bool")
                                                                    )
                    | _ -> raise(DynamicTypeError "set_esists: ha fallito perchè il primo parametro deve essere una closure o rec_closure")
                )                            
    and set_filter (closure: evT) (set_v: set_val) : set_val = 
        match set_v with
        | EmptyV -> EmptyV (* se l'insieme è vuoto restituisce l'insieme vuoto *)
        | ConsV (v', s') -> (* se l'insieme invece non è vuoto ... *)
                (
                    match closure with
                    | Closure (param, bodyFun, declEnvFun, _, _) ->
                                                                    let actualEnv = bind declEnvFun param v' in (* aggiungo il binding tra il parametro formale ed attuale all'ambiente *)
                                                                    (
                                                                        match eval bodyFun actualEnv with (* calcolo la funzione sul primo parametro che mi restituisce true o false *)
                                                                        | Bool(value) when value = true ->
                                                                                                        ConsV(v', set_filter closure s') (* se l'elemento rispetta il predicato, lo aggiungo al cons insieme alla chiamata ricorsiva sul resto dell'insieme *)
                                                                                
                                                                        | _ -> raise(DynamicTypeError "set_filter: la valutazione della funzione non ha ritornato un bool")
                                                                    )
                    | RecClosure (ideFun, param, bodyFun, declEnvFun, _, _) ->
                                                                    let recEnv = bind declEnvFun ideFun closure in (* aggiungo il binding tra il parametro formale ed attuale all'ambiente *)
                                                                    let actualEnv = bind recEnv param v' in
                                                                    (
                                                                        match eval bodyFun actualEnv with (* calcolo la funzione sul primo parametro *)
                                                                        | Bool(value) when value = true ->
                                                                                                        ConsV(v', set_filter closure s') (* se l'elemento rispetta il predicato, lo aggiungo al cons insieme alla chiamata ricorsiva sul resto dell'insieme *)
                                                                        | _ -> raise(DynamicTypeError "set_filter: la valutazione della funzione non ha ritornato un bool")
                                                                    )
                    | _ -> raise(DynamicTypeError "set_filter: ha fallito perchè il primo parametro deve essere una closure o rec_closure")
                )
    and set_map (closure: evT) (set_v: set_val) : set_val = 
        match set_v with
        | EmptyV -> EmptyV (* se l'insieme è vuoto restituisce l'insieme vuoto *)
        | ConsV (v', s') -> (* se l'insieme invece non è vuoto ... *)
                (
                    match closure with
                    | Closure (param, bodyFun, declEnvFun, _, _) ->
                                                                    let actualEnv = bind declEnvFun param v' in (* aggiungo il binding tra il parametro formale ed attuale all'ambiente *)
                                                                    
                                                                    let returnFun =  eval bodyFun actualEnv in  (* calcolo la funzione sul primo parametro, ottenendo un valore *)

                                                                    ConsV(returnFun, set_map closure s') (*aggiungo il valore calcolato al cons e concateno la chiamata della set_map sul resto dell'insieme *)                                                                    
                    | RecClosure (ideFun, param, bodyFun, declEnvFun, _, _) ->
                                                                    let recEnv = bind declEnvFun ideFun closure in (* aggiungo il binding tra il parametro formale ed attuale all'ambiente *)
                                                                    
                                                                    let actualEnv = bind recEnv param v' in
                                                                    
                                                                    let returnFun = eval bodyFun actualEnv in

                                                                    ConsV(returnFun, set_map closure s') (*aggiungo il valore calcolato al cons e concateno la chiamata della set_map sul resto dell'insieme *)                                        
                    | _ -> raise(DynamicTypeError "set_map: ha fallito perchè il primo parametro deve essere una closure o rec_closure")
                );;

(* === TESTS === *)
let env0 = empty_env;; (* Ambiente vuoto *)

(* testo la somma di 10 e 20 *)
let result = eval ( Add(CstInt 10, CstInt 20) ) env0;;
assert (result = Int 30);;

(* testo la introduzione di una variabile var = 10 *)
let result = eval ( Let( "var", CstInt 10, Den("var") ) ) env0;;
assert (result = Int 10);;

(* testo la somma della variabile n=10 e della variabile m=30 *)
let result = eval ( Add( Let( "n", CstInt 10, Den("n") ) , Let( "m", CstInt 30, Den("m") ) ) ) env0;;
assert (result = Int 40);

(* testo la Apply con una funzione che incrementa di 2 l'argomento passato *)
let result = eval ( Apply ( Fun ( "x", Add ( Den "x", CstInt 2 ), IntType, IntType ), CstInt 2 ) ) env0 in
assert (result = Int 4);;

(* testo la Exist con una funzione che torna sempre true applicata su un Singleton *)
let result = eval ( Exists ( Fun ( "buddy_param", Equals ( CstInt 1, CstInt 1 ), IntType, BoolType ), (Singleton (IntType, CstInt 100)) ) ) env0 in
assert (result = Bool true);;

(* testo la Exist con una funzione che torna true se l'argomento passato è uguale a 100 su un Singleton con solo l'elemento 100 *)
let result = eval ( Exists ( Fun ( "x", Equals ( Den "x", CstInt 100 ), IntType, BoolType ), (Singleton (IntType, CstInt 100)) ) ) env0 in
assert (result = Bool true);;

(* testo la Exist con una funzione che torna true se l'argomento passato è uguale alla stringa "ciao" su un Set Vuoto *)
let result = eval ( Exists ( Fun ( "y", CstTrue, StringType, BoolType ), EmptySet StringType ) ) env0 in
assert (result = Bool false);;

(* testo la ForAll con una funzione che torna true se l'argomento passato è uguale alla stringa "ok" su un Set creato con Of *)
let result = eval ( ForAll ( Fun ("arg", EqualsString ( Den "arg", CstString "ok" ), StringType, BoolType ), Of (StringType, Cons( CstString "ciao", Cons(CstString "ok", Empty))))) env0 in
assert (result = Bool false);;

(* testo la Union su due Singleton di tipo stringa con lo stesso elemento, lo rimuovo con la Remove e verifico se il set è vuoto con la IsEmpty *)
let result = eval ( IsEmpty ( Remove ( CstString "ciccio", Union ( Singleton ( StringType, CstString "ciccio" ),
                                              Singleton ( StringType, CstString "ciccio") ) ) ) )  env0 in
assert (result = Bool true);;

(* testo la Intersection su due singleton con elementi diversi di tipo booleano, chiamando poi la IsEmpty *)
let result = eval ( IsEmpty ( Intersection ( Singleton ( BoolType, CstTrue ), Singleton ( BoolType, CstFalse ) ) ) ) env0 in
assert (result = Bool true);;

(* testo la Contains, verificando su un insieme di tipo intero creato con la Of se contiene un intero *)
let result = eval ( Contains( CstInt 14, Of (IntType, Cons( CstInt 10, Cons(CstInt 14, Empty))) ) ) env0 in
assert (result = Bool true);;

(* testo la Subset verificando se un insieme vuoto di tipo int è sottoinsieme di un Singleton di tipo int, e aggiungo il Not all'inizio *)
let result = eval ( Not ( Subset ( EmptySet IntType, Singleton ( IntType, CstInt 100 ) ) ) ) env0 in
assert (result = Bool false);;

(* testo la Filter con una funzione che ritorna true se l'argomento passato è uguale a 1 oppure a zero su un Singleton con solo 1,
   dopodichè verifico se l'insieme è vuoto *)
let test_pred = Fun ("arg", Or ( Equals ( Den "arg", CstInt 1 ), IsZero ( Den "arg" ) ), IntType, BoolType );;
let result = eval ( IsEmpty ( Filter ( test_pred, Singleton ( IntType, CstInt 1 ) ) ) ) env0 in
assert (result = Bool false);;

(* testo la ForAll su un Singleton avente l'intero 4 a cui aggiungo invece 1 *)
let result = eval ( ForAll ( test_pred, Insert ( CstInt 1 , Singleton ( IntType, CstInt 4 ) ) ) ) env0 in
assert (result = Bool false);;

(* testo il MinOf su un Singleton avente un intero 1000 a cui aggiungo prima l'intero 5 *)
let result = eval ( MinOf ( Insert ( CstInt 5, Singleton ( IntType, CstInt 1000 ) ) ) ) env0 in
assert (result = Int 5);;

(* testo la MaxOf su un Singleton avente un intero 15 a cui aggiungo prima l'intero 14 *)
let result = eval ( MaxOf ( Insert ( CstInt 14, Singleton (IntType, CstInt 15 ) ) ) ) env0 in
assert (result = Int 15);;

(* testo la Map con una funzione che moltiplica per 2 l'argomento, su un Singleton di intero 2 a cui aggiungo sia 4 che 8, e poi calcolo il MaxOf *)
let times_2 = Fun ( "arg", Times ( Den "arg", CstInt 2 ), IntType, IntType );;
let result = eval ( MaxOf ( Map (times_2, Insert ( CstInt 8, Insert ( CstInt 4, Singleton ( IntType, CstInt 2 ) ) ) ) ) ) env0 in
assert (result = Int 16);;
