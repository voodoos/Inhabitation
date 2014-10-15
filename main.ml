(* Types *)
(* Simple implementation des multisets *)
type 'a multiset =
  Empty
| Cons of 'a * 'a multiset

(* Types multisets *)
type multisetType = sType multiset
and sType = 
  Var of char
| Fleche of multisetType * sType

(* Environements *)
type environment = (int * multisetType) list

(* Approximate normal forms *)
type anf = 
Omega
| N of n
and n = 
  Lambda of int * n
| L of l
and l =
  Var of int
| App of l * anf


(* Lambda terms with Omega *)
type term =
 V of int
| Omg
| Lamb  of int * term
| A of term * term

(* Chemins *)
type path = 
DeadEnd
| End
| Final
| Abs of path
| Union of path
| Prefix of path * path
| Head of path

(* Converti un multiset en une liste (tr) *)
let msToList ms = 
  let rec aux acc = function
    Empty -> acc
  | Cons(x, ms) -> aux (acc@[x]) ms
  
  in aux [] ms

(* Créé une liste de n listes vides (tr) *)
let initList n = 
  let rec aux acc = function
      0 -> acc
    | m -> aux ([]::acc) (m-1)

  in aux [] n

(* Créé une liste de n multisets vides (tr) *)
let initMS n = 
  let rec aux acc = function
      0 -> acc
    | m -> aux (Empty::acc) (m-1)

  in aux [] n

(* Renvoie le nombre d'éléments d'un multiset (tr) *)
let sizeOfMS ms = 
  let rec aux acc =  function
    Empty -> acc
  | Cons(_, tl) -> aux (acc+1) tl

  in aux 0 ms

(* Contactenation de deux multiset (tr) *)
let rec concat m1 m2 = match m1 with
    Empty -> m2
  | Cons(h, t) -> concat t (Cons(h, m2))

(* Partitions d'un multiset *)
let rec splitsN ms n = 
   (* Ajoute un élément à une découpe de toutes les façons possibles (tr) *)
   let rec add decoupe acc acc2 x = match decoupe with 
       [] -> acc2
     | h::tl -> add tl (h::acc) ((acc@(Cons(x, h)::tl))::acc2) x in

  match ms with
    Empty -> [initMS n] (* [[ [];[];[];...;[] ]] *)
  | Cons(h, tl) -> let reste = (splitsN tl n) in
	     List.concat (List.map (fun d -> (add d [] [] h)) reste)

(* let test0 = splitsN (Cons(1, Cons(2, Empty))) 3 *)


(* Liste les extractions possibles d'un multiset (tr) *)
let extractMS l =
  let rec aux acc acc2 = function
  Empty -> acc2
  | Cons(h, t) -> (aux (Cons(h, acc)) ((h, concat acc t)::acc2) t) in
  aux Empty [] l

(* let test3 = extractMS (Cons(1, Cons(2, Cons(3, Cons(4, Empty))))) *)



(* Liste les découpes possibles d'un environnement *)
let rec envSplitsN n = function
  [] -> [initList n]
  | (x, tys)::tl -> let decoupes = splitsN tys n and reste = envSplitsN n tl in
		    (* On rétablit la structure (x : types) *)
		    let decoupesX = List.map (fun paquets -> 
		      List.map (fun paquet -> (x, paquet)) paquets) decoupes in
		    (* On ajoute au reste les différents choix pour cette variable *)
		    List.concat (
		      List.map (fun envs -> (* Pour chaque choix pour x on divise encore les environements *)
			List.map (fun decoupeX -> 
			  List.map2 (fun x env -> 
			    if snd(x) = Empty then env else (x::env)) decoupeX envs) decoupesX) reste)
		    
(* let test22 = envSplitsN 3 [(1, Cons(Var('a'), Cons(Var('b'), Empty)));(2, Cons(Var('c'), Empty))] *)

(* Liste les extractions possibles de couples var /type d'un env (tr) *)
let envExtracts (env : environment) = 
  let rec aux acc acc2 = function
    [] -> acc2
  | (x, types)::t -> (aux ((x, types)::acc) ((List.map (fun ex -> let (e, tail) = ex in 
					 let elt = Cons(e, Empty) in 
					 match tail with
					   Empty -> ((x, elt), t@acc)
					 | _ -> ((x, elt), (x, tail)::t@acc)) (extractMS types))@ acc2) t) in
  aux [] [] env

(* let test4 = envExtracts [(1, Cons(Var('a'), Cons(Var('b'), Empty)));(2, Cons(Var('c'), Empty));] *)

(* Fusionne deux environnements (tr) *)
let rec envFusion (env0 : environment) (env1 : environment) = 
  let rec aux elt acc = function 
      [] -> elt::acc
    | (x, type0)::tl when x = fst(elt) -> acc@((x, concat type0 (snd(elt)))::tl)
    | h::tl -> aux elt (h::acc) tl

  in match env0 with
    [] -> env1
  | h::t -> envFusion t (aux h [] env1)

(* let test5 = envFusion [(1, Cons(Var('a'), Cons(Var('b'), Empty)));(2, Cons(Var('c'), Empty));] [(1, Cons(Var('c'), Empty))] *)


let rec notIn x = function
    Omega -> true
  | N(n) -> niN x n
and niN x = function
    Lambda(y, n) when y = x -> false
  | Lambda(_, n) -> niN x n
  | L(l) -> niL x l
and niL x = function
    Var(y) when x = y -> false
  | Var(_) -> true
  | App(l, a) -> (niL x l)&&(notIn x a)

(* Alpha conversion *)
let rec alpha x y = function
  | Omega -> Omega
  | N(n) -> N(alphaN x y n)
and alphaN x y = function
    Lambda(c, n) when c = x && niN y n-> Lambda(y, alphaN x y n)
  | Lambda(c, n) -> Lambda(c, alphaN x y n)
  | L(l) -> L(alphaL x y l)
and alphaL x y = function
    Var(z) when z = x -> Var(y)
  | Var(z) -> Var(z)
  | App(l, a) -> App(alphaL x y l, alpha x y a)

let tititoto = alpha 1 2  (N(Lambda(1, L(Var(2)))))


let rec anfToString  = function
    Omega -> "Omega"
  | N(n) -> nToString n
and nToString = function
  | Lambda(x, n) -> "Lambda ("^string_of_int x^", "^nToString n^")"
  | L(l) -> lToString l
and lToString = function
    Var(x) -> string_of_int x
  | App(l, anf) -> "App("^lToString l^", "^anfToString anf^")"


(* Max of two anf with path info*)
let rec compAnfCouple a b = match a, b with
  | (Omega,_), _ -> b
  |  _, (Omega, _) -> a
  | (N(na),pa), (N(nb), pb) -> let r = compNfCouple (na, pa) (nb, pb) in (N(fst(r)),snd(r))
and compNfCouple a b =  match a, b with
    (Lambda(ca, na), pa), (Lambda(cb, nb), pb) -> let r = compNfCouple (na, pa) ((alphaN cb ca nb), pb) in
						  (Lambda(ca, fst(r)), snd(r))
  | (L(la), pa), (L(lb), pb) -> let r = compLfCouple (la, pa) (lb, pb) in (L(fst(r)), snd(r))
  | _, _ -> failwith ("Arg no Least upper bound found !"^(nToString (fst(a)))^" "^(nToString (fst(b))))

and compLfCouple a b = match a, b with
    (Var(ca), pa), (Var(cb), pb) when ca = cb -> (Var(ca), pa)
  | (App(la, anfa), pa), (App(lb, anfb), pb) -> let r = (compLfCouple (la, pa) (lb, pb))
  and r2 = compAnfCouple (anfa, pa) (anfb, pb) in (App(fst(r), fst(r2)), snd(r2))
  | _, _ -> (Var(200), End) (*failwith "Arg no Least upper bound found ! 2"*)



let rec compAnfsCouples = function
[] -> (Omega, End)
 | h::tl -> compAnfCouple (N(fst(h)), snd(h)) (compAnfsCouples tl)

(* anf -> lambdaterms *)
let rec toLambda = function
Omega -> Omg
  | N(n) -> toln n
and toln = function
Lambda(x, n) -> Lamb(x, toln n)
  | L(l) -> toll l
and toll = function
Var(x) -> V(x)
  |App(l, a) -> A(toll l, toLambda a)


(* Affichage *)
let rec stringOfSType (t : sType) = match t with
    Var(c) -> String.make 1  c
  | Fleche(ms, s) -> (stringOfMSType ms)^" -> "^ stringOfSType s

and stringOfMSType mst =
  
  let rec aux = function
    Empty -> "]"
  | Cons(s, ms) -> if ms != Empty then stringOfSType s ^ ";" ^ (stringOfMSType ms) 
    else stringOfSType s^"]"
  in "["^aux mst


let rec stringOfEnv e =
  let rec aux =  function 
    [] -> "]"
  | (x, type0)::tl -> if List.length tl  > 0 then 
      "(" ^ (string_of_int x) ^ ": " ^ (stringOfMSType type0) ^ ");" ^ aux tl
    else "(" ^ (string_of_int x) ^ ": " ^ (stringOfMSType type0) ^ ")]"
  in "["^aux e


let rec printAnfList = function
    [] -> ()
  | h::tl -> (print_string (nToString h));(print_string ";");printAnfList tl





(* Inhabitation algorithm *)
let inhabitation (env: environment) (type0 : sType) (minFresh : int)  =
  let rec t (env: environment) (type0 : sType) (fresh : int) =

    print_string ("T : " ^ (stringOfEnv env) ^ ", " ^ (stringOfSType type0) ^ "\n");

    match env, type0 with
    (* Si type fleche, alors (abs) s'applique, de plus on doit appliquer (Head) pour chaque extraction possible d'un couple Var / Type de l'environnement *)
      (* ABS *)
      ([], Fleche(type1, type2)) -> abs env fresh type1 type2
      (* ABS + HEAD *)
    | (_::_, Fleche(type1, type2)) -> (abs env fresh type1 type2)@(head env type0 fresh)
      (* HEAD *)
    | (_::_, _) -> head env type0 fresh
    | (_,_) -> []


  and abs (env : environment) (fresh : int) (type0 : multisetType) (type1 : sType) = 

    print_string ("ABS : " ^ (stringOfEnv env) ^ ", " ^ (stringOfMSType type0) ^ ", " ^ (stringOfSType type1) ^ "\n");

    (* On prend une variable fraiche et on appelle récursivement t *)
    if type0 = Empty then
      List.map (fun elt -> (Lambda(fresh, fst(elt)), Abs(snd(elt))) ) (t env type1 (fresh + 1))
    else
      List.map (fun elt -> (Lambda(fresh, fst(elt)), Abs(snd(elt))) ) (t ((fresh, type0)::env) type1 (fresh + 1))

  and head (env : environment) (type0 : sType) fresh = 

    print_string ("HEAD : " ^ (stringOfEnv env) ^ ", " ^ (stringOfSType type0) ^ "\n");

    (* On regarde toutes les extractions possible d'un couple var / type *)
    let extracts = envExtracts env in

    (* On applique (head) pour chaque extract ( ->  ((x, [type]), envTail) ) *)
    List.concat 
      (List.map 
	 (fun extract -> let type1 = match (snd(fst(extract))) with
	   Cons(type1, Empty) -> type1
	 | _ -> assert false 
			 in
			 let res = h [fst(extract)] (snd(extract)) (Var(fst(fst(extract)))) type1 type0 fresh in
			 (* On rajoute le path *)
			 List.map (fun termPath -> (fst(termPath), Head(snd(termPath))) ) res
	 ) 
	extracts)
    
  and h (env1 : environment) (env2 : environment) (lf : l) (type1 : sType) (type2 : sType) (fresh : int) =

    print_string ("H : E1=" ^ (stringOfEnv env1) ^ " E2="^ (stringOfEnv env2)^ " T1=" ^ (stringOfSType type1) ^ " T2=" ^ (stringOfSType type2)^ ", LF="^lToString lf^"\n");

    match env2, type1 with
    (* FINAL + PREFIX *)
      ([], Fleche(typeA, typeS)) -> (final type1 type2 lf)@(prefix env1 env2 lf typeA typeS type2 fresh)
    (* FINAL *)
    | ([], type1)-> final type1 type2 lf
    (* PREFIX *)
    | (_, Fleche(typeA, typeS)) -> prefix env1 env2 lf typeA typeS type2 fresh
    | (_, _) -> []

  and final (type1 : sType) (type2 : sType) (lf : l) =
    print_string ("FINAL : " ^ (stringOfSType type1) ^ ", " ^ 
		     (stringOfSType type2) ^ "--> "^(lToString lf)^"\n");
    if type1 = type2  then [(L(lf), Final)] else []

  and prefix (env1 : environment)  (env2 : environment) (lf : l) (type1 : multisetType) (type2 : sType) (type3 : sType) (fresh : int) = 
 
    print_string ("PREFIX : " ^ (stringOfEnv env1) ^ ", "^ (stringOfEnv env2)^ ", " ^ (stringOfMSType type1) ^ ", " ^ (stringOfSType type2) ^ ", " ^ (stringOfSType type3)^ "\n");

    let decoupes = envSplitsN 2 env2 in
    (* Pour chaque découpage possible, on cherche les termes que trouve TI puis on appelle h *)
    
    List.concat (List.map (fun (envs : environment list) -> 
	let env20 = (List.hd envs) and env21 = (List.hd (List.tl envs)) in
	
        (* On appelle union, et pour chaque résultat de ti on appelle h *)
	(* UNION *)
	let res = union env20 type1 fresh in (*N(L(Var('m')))*)
	if snd(res) != DeadEnd then
	  let res2 = h (envFusion env1 env20) env21 (App(lf, fst(res))) type2 type3 fresh in
	  (* On rajoute le path *)
	  List.map (fun termPath -> (fst(termPath), Prefix(snd(res), snd(termPath))) ) res2
	else []
    )
    decoupes)

  and union (env0 : environment) (type0 : multisetType) (fresh : int) = 
    let i = sizeOfMS type0 in
    print_string ("UNION : " ^ (stringOfEnv env0) ^ ", " ^ (stringOfMSType type0) ^ "\n");
    
	(* On cherche toutes les partitions en i elements de l'environment *)
    let partitions = envSplitsN i env0 in
	(* Pour chaque melange et chaque type on tente de touver des termes qui font l'affaire: *)
    let nList = List.concat (List.concat (List.map (fun partition -> 
      List.map2 (fun partie type0 -> t partie type0 fresh) partition (msToList type0)) partitions)) in
    
    print_string "Anf trouvees: ";
	printAnfList (List.map (fun t -> fst(t)) nList);
    
    print_string "\n";
    
    if(List.length nList > 0 || i = 0) then 
      begin
	let r = compAnfsCouples nList in
	(fst(r),Union(snd(r)))
      end
    else (Omega, DeadEnd)
      
  in (* On remplace les anf par de simples termes *)
  List.map (fun couple -> (toLambda (N(fst(couple))),snd(couple))) (t env type0 minFresh)

let (a : sType) = Var('a')
let (b : sType) = Var('b')
let (c : sType) = Var('c')
let (d : sType) = Var('d')
let (e : sType) = Var('e')

let afa = Cons(Fleche(Cons(a, Empty), a),Empty)

let sgl i = Cons(i, Empty)

(*
let ex1 = inhabitation [] a 1
let ex2 = inhabitation [(1, Cons(b, Empty))] a 1
let ex3 = inhabitation [(1, Cons(a, Empty))] a 1
let ex4 = inhabitation [] (Fleche(sgl a, a)) 1
let ex4b = inhabitation [] (Fleche(Cons( a, Cons(b, Empty)), a)) 1
let ex5 = inhabitation [] (Fleche(Cons(Fleche(Empty, a),Empty), a)) 1
let ex6 = inhabitation [] (Fleche(Cons(a,Cons(Fleche(sgl a, a), Empty)), a)) 1
let ex7 = inhabitation [(1, Cons(Fleche(sgl a, a), Empty))] a 2
let ex7b = inhabitation [(1, Cons(Fleche(sgl a, a), Cons(b, Empty)))] b 2
let ex8 = inhabitation [(1, Cons(a, afa))] a 2
let ex9 = inhabitation [(1, afa)] (Fleche(sgl a, a)) 2
let ex11 = inhabitation [(1, afa); (2, afa); (3, sgl a)] a 4
let ex12 = inhabitation [] (Fleche(Cons(Fleche(Cons(a, Empty), a), Empty), Fleche(Cons(a, Empty), a))) 1
*)
let ex = inhabitation [] (Fleche(Cons(Fleche(Cons(a, sgl a), a), sgl a), Fleche(sgl a, a))) 1

(* let ex12 = inhabitation [] 
  (Fleche(Cons(
  Fleche(Cons(
    Fleche(
      Cons((Fleche(Cons(Fleche(Cons(a, Empty), a), Empty), Fleche(Cons(a, Empty), a))), Empty)
	, 
      (Fleche(Cons(Fleche(Cons(a, Empty), a), Empty), Fleche(Cons(a, Empty), a)))
    ), Empty)
, Fleche(
      Cons((Fleche(Cons(Fleche(Cons(a, Empty), a), Empty), Fleche(Cons(a, Empty), a))), Empty)
	, 
      (Fleche(Cons(Fleche(Cons(a, Empty), a), Empty), Fleche(Cons(a, Empty), a)))
    )), Empty),

Fleche(Cons(
    Fleche(
      Cons((Fleche(Cons(Fleche(Cons(a, Empty), a), Empty), Fleche(Cons(a, Empty), a))), Empty)
	, 
      (Fleche(Cons(Fleche(Cons(a, Empty), a), Empty), Fleche(Cons(a, Empty), a)))
    ), Empty)
, Fleche(
      Cons((Fleche(Cons(Fleche(Cons(a, Empty), a), Empty), Fleche(Cons(a, Empty), a))), Empty)
	, 
      (Fleche(Cons(Fleche(Cons(a, Empty), a), Empty), Fleche(Cons(a, Empty), a)))
    )))

)

 1*)
