type nfa = {                      (* automate fini non déterministe *)
  nb_etats : int;
  initiaux : bool array;
  finaux : bool array;
  transitions : (char * int) list array 
}

type automate_lin = {              (* automate linéarisé *)
  nb_etats : int;                 
  initial : int;                   (* état = entier *)
  tab_car : char array;            (* tableau de caractères tel que dans la case i on a le caractère du ième état marqué, pour epsilon char_of_int 0 = \000*)                   
  finaux : bool array;             (* tableau de taille nb_etats, dans lequel la case numéro i indique si l'etats i est terminal ou non *)
  transitions : bool array array   (* matrice de taille |Q|*|Q| dont l'élement (i, j) indique si il y une transition vers j à partir de i*)
}

type 'a regexp =
  |Vide
  |Epsilon
  |Lettre of 'a
  |Union of 'a regexp * 'a regexp
  |Concat of 'a regexp * 'a regexp
  |Kleene of 'a regexp


(*==============================================================   Langages locaux   =========================================================================================*)

let rec nb_lettres expr =
  match expr with
  |Vide -> 0
  |Epsilon -> 0
  |Lettre(c) -> 1
  |Union(expr1, expr2) -> (nb_lettres expr1) + (nb_lettres expr2)
  |Concat(expr1, expr2) -> (nb_lettres expr1) + (nb_lettres expr2)
  |Kleene(expr) -> nb_lettres expr

  
let linearisation expr =
  let indice = ref (nb_lettres expr + 1) in (*mon premier numéro sera 1 pour laisser la place à l'état epsilon*)
  let rec aux expr =
    match expr with
    |Vide -> Vide
    |Epsilon -> Epsilon
    |Lettre(c) -> decr indice; Lettre (c, !indice)
    |Union(expr1, expr2) -> Union ( aux expr1, aux expr2 )
    |Concat(expr1, expr2) -> Concat ( aux expr1, aux expr2)
    |Kleene(e) -> Kleene(aux e)
  in
  aux expr

let rec union l1 l2 = 
  match l1 with
  | []    -> l2
  | x :: xs -> 
    if List.mem x xs then (union xs l2)
    else x :: (union xs l2)

let rec produit_cartesien l1 l2 =
  match l1 with
  | []    -> []
  | x :: xs -> (List.map (fun y -> (x, y)) l2) @ (produit_cartesien xs l2)

let rec contient_eps exp =
  match exp with
  |Vide           -> false
  |Epsilon        -> true
  |Lettre(a)      -> false
  |Union(e1, e2)  -> contient_eps e1 || contient_eps e2
  |Concat(e1, e2) -> contient_eps e1 && contient_eps e2
  |Kleene(e1)     -> true

let rec est_vide exp = 
  match exp with
  |Vide           -> true
  |Epsilon        -> false
  |Lettre(a)      -> false
  |Union(e1, e2)  -> est_vide e1 && est_vide e2
  |Concat(e1, e2) -> est_vide e1 || est_vide e2
  |Kleene(e1)     -> false


let rec premieres_lettres exp =
  match exp with
  |Vide |Epsilon  -> []
  |Lettre(a)      -> [a]
  |Union(e1, e2)  -> union (premieres_lettres e1) (premieres_lettres e2)
  |Concat(e1, e2) -> 
    if contient_eps e1 then union (premieres_lettres e1) (premieres_lettres e2)
    else premieres_lettres e1
  |Kleene(e1)     -> premieres_lettres e1
  
let rec dernieres_lettres exp = 
  match exp with
  |Vide |Epsilon  -> []
  |Lettre(a)      -> [a]
  |Union(e1, e2)  -> union (dernieres_lettres e1) (dernieres_lettres e2)
  |Concat(e1, e2) -> 
    if contient_eps e2 then union (dernieres_lettres e1) (dernieres_lettres e2)
    else dernieres_lettres e2
  |Kleene(e1)     -> dernieres_lettres e1
  
let rec facteurs exp =
  match exp with
  |Vide |Epsilon  -> []
  |Lettre(a)      -> []
  |Union(e1, e2)  -> union (facteurs e1) (facteurs e2)
  |Concat(e1, e2) -> 
    if est_vide e1 || est_vide e2 then []
    else 
    let l = union (facteurs e1) (facteurs e2) in
    let entre_deux = produit_cartesien (dernieres_lettres e1) (premieres_lettres e2) in
    union l entre_deux
  |Kleene(e1)     -> 
    let entre_deux = produit_cartesien (dernieres_lettres e1) (premieres_lettres e1) in
    union (facteurs e1) entre_deux


(*==============================================================   Automate de Glushkov   =========================================================================================*)


let create_autod exprlin = (*fonction qui crée l'automate déterministe (avant la délinéarisation) à partir de la regexpr linéarisée*)
  let nb_lettres = nb_lettres exprlin in
  let nb_etats = nb_lettres + 1 in (*+1 pour pouvoir mettre l'état epsilon*)
  let initial = 0 in   (*epsilon*)
  let tab_char = Array.make nb_etats (char_of_int 0) in
  let rec remplir_tab_char exprlin =
    match exprlin with
    |Vide -> ()
    |Epsilon -> ()
    |Lettre(c, i) -> tab_char.(i) <- c
    |Union(expr1, expr2) -> remplir_tab_char expr1; remplir_tab_char expr2
    |Concat(expr1, expr2) -> remplir_tab_char expr1; remplir_tab_char expr2
    |Kleene(e) -> remplir_tab_char e
  in
  remplir_tab_char exprlin;
  
  let les_facteurs = facteurs exprlin in
  let transitions = Array.make_matrix nb_etats nb_etats false in
  let rec remplir_transitions les_facteurs =
    match les_facteurs with
    |[] -> ()
    |( (_, a), (_, b) ):: xs -> transitions.(a).(b) <- true; remplir_transitions xs
  in
  remplir_transitions les_facteurs;
  let les_prefixes = premieres_lettres exprlin in
  let rec remplir_transitions les_prefixes =
    match les_prefixes with
    |[] -> ()
    |(_, a) :: xs -> transitions.(0).(a) <- true; remplir_transitions xs
  in
  remplir_transitions les_prefixes;
  let les_suffixes = dernieres_lettres exprlin in
  let finaux = Array.make nb_etats false in
  let rec remplir_finaux les_suffixes =
    match les_suffixes with
    |[] -> ()
    |(_, a) :: xs -> finaux.(a) <- true; remplir_finaux xs
  in
  if contient_eps exprlin then finaux.(0) <- true; (* T = Unions(suffixe, eps) si eps appartient au langage, T = suffixe sinon*)
  remplir_finaux les_suffixes;
  {
    nb_etats = nb_etats;
    initial = initial;
    tab_car = tab_char;
    finaux = finaux;
    transitions = transitions
  }


let delinearise (abs: automate_lin): nfa =
  let n = abs.nb_etats in
  let initiaux = Array.init n (fun x -> (x = 0)) in
  let finaux = abs.finaux in
  let transitions = Array.make n [] in
  for i = 0 to n-1 do  (*on parcourt toutes les transitions*)
    for j = 0 to n-1 do
      if abs.transitions.(i).(j) then begin
        transitions.(i) <- (abs.tab_car.(j), j) :: transitions.(i)  (*on passe par le caractère abs.tab_car.(j) pour aller à j à partir de i*)
      end
    done
  done;
  {nb_etats = n; initiaux = initiaux; finaux = finaux; transitions = transitions}


let glushkov e =  delinearise (create_autod (linearisation e)) 


(*==============================================================   Reconnaissance de mots   =========================================================================================*)


let char_list_of_string s = List.rev (String.fold_left (fun acc c -> c::acc) [] s) 

exception Non_trouve
let delta (auto: nfa) etat c =
  let rec recherche l c =
    match l with
    |[] -> raise Non_trouve
    |(d, new_etat) :: xs when d = c -> new_etat
    |_ :: xs -> recherche xs c
  in
  recherche auto.transitions.(etat) c

let rec char_list u = List.rev (String.fold_left (fun acc x -> x :: acc) [] u) (*donne la liste des caractères de u *)

let is_etat_terminal tab terminaux =
  let i = ref 0 in
  let n = Array.length tab in
  while !i < n && not (tab.(!i) && terminaux.(!i)) do
    incr i
  done;
  !i < n

let delta_chapeau_etoile (auto: nfa) mot =   (* mot est ici une liste *)
  let rec aux tab mot = 
    match mot with
    |[]            -> tab
    |lettre :: reste ->
    let arrivee = Array.make auto.nb_etats false in
    for i = 0 to (Array.length tab) - 1 do
      if tab.(i) then 
        let j = delta auto i lettre in
        arrivee.(j) <- true
    done; 
    aux arrivee reste
  in 
  let initial = Array.make auto.nb_etats false in 
  initial.(0) <- true;
  aux initial mot

let est_reconnu (auto_nd: nfa) mot = 
  try is_etat_terminal (delta_chapeau_etoile auto_nd (char_list_of_string mot)) auto_nd.finaux with
  |Non_trouve -> false


(*==============================================================   Analyse de l'entrée de l'utilisateur  =============================================================================*)
(* fonction qui transforme l'entrée de l'utilsateur (en notation postfixe par ex abc@|) en expression régulière avec le type regexp*)

let transform_to_regexp u =            (*u est une expression régulière entrée par l'utilisateur, en notation postfixe*)
  let l = char_list u in    
  let p = Stack.create () in     
  let rec aux l =
  match l with
  |[]    -> let a = Stack.pop p in a
  |x::xs -> 
    if x = '|' then 
      let e1 = Stack.pop p in
      let e2 = Stack.pop p in 
      Stack.push (Union(e2, e1)) p;
      aux xs

    else if x = '@' then 
      let e1 = Stack.pop p in
      let e2 = Stack.pop p in 
      Stack.push (Concat(e2, e1)) p;
      aux xs

    else if x = '*' then 
      let exp = Stack.pop p in
      Stack.push (Kleene(exp)) p;
      aux xs

    else if x = '?' then                              (* exp? = exp|epsilon *)
      let exp = Stack.pop p in 
      Stack.push (Union(exp, Epsilon)) p;
      aux xs

    else if x = '.' then                              (* '.' indique n'importe quelle lettre, càd a|b|c|d|...|x|y|z*)
      let rec transform_to_regexp_union_point i acc =
        if i < 97 then acc
        else 
          let c = char_of_int i in
          transform_to_regexp_union_point (i-1) (Union(Lettre(c), acc))
      in 
      let res = transform_to_regexp_union_point 121 (Lettre(char_of_int 122))
      in Stack.push res p;
      aux xs

    else begin 
      Stack.push (Lettre(x)) p; 
      aux xs 
    end
  in aux l

  
(*==============================================================   Squelette du projet  =============================================================================*)

let process_line auto line = if est_reconnu auto line then Printf.printf "%s\n%!" line

(* Lecture de l'entrée, ligne par ligne *)
let process auto input =
  try
    while true do
      let line = Stdlib.input_line input in
      process_line auto line
    done
  with End_of_file -> ()

let main () =
  (* Vérifie que l'expression régulière est bien présente en premier
    argument. Sinon, on affiche un message indiquant comment utiliser
    ce programme et on quitte avec un code d'erreur de `1`. *)
  let argc = Array.length Sys.argv in
  if argc < 2 || argc > 3 then begin
    Printf.printf "usage : %s regex [file]\n%!" Sys.argv.(0);
    exit 1
  end;
  (* S'il y a un deuxième argument c'est qu'il faut lire dans ce
    fichier, sinon, on utilise l'entrée standard. *)
  let input =
    if (argc = 3) then begin
      Stdlib.open_in Sys.argv.(2)
    end else
      Stdlib.stdin
  in
  Printf.printf
    "* Regexp you entered is '%s'\n* Reading from %s\n\n%!"
    Sys.argv.(1)
  
    (if argc = 3 then Sys.argv.(2) else "stdin");

  let exp_lin = transform_to_regexp Sys.argv.(1) in
  let res = glushkov exp_lin in
  Printf.printf "\n";
  process res input;
  if argc = 3 then Stdlib.close_in input

let () = main ()
