(* Simple implementation des multisets *)
type 'a multiset =
  Empty
| Cons of 'a * 'a multiset

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



(* Types *)
type multisetType = sType multiset
and sType = 
  Var of char
| Fleche of multisetType * sType

type environment = (char * multisetType) list


(* Détermine la vidité d'un environement (tr) *)
let rec envIsEmpty = function
  | [] -> true
  | (_, Empty)::tl -> envIsEmpty tl
  | _ -> false

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
			  List.map2 (fun x env -> x::env) decoupeX envs) decoupesX) reste)
		    
(* let test22 = envSplitsN 3 [('x', Cons(Var('a'), Cons(Var('b'), Empty)));('y', Cons(Var('c'), Empty))] *)


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

(* let test4 = envExtracts [('x', Cons(Var('a'), Cons(Var('b'), Empty)));('y', Cons(Var('c'), Empty));] *)

(* Fusionne deux environnements (tr) *)
let rec envFusion (env0 : environment) (env1 : environment) = 
  let rec aux elt acc = function 
      [] -> elt::acc
    | (x, type0)::tl when x = fst(elt) -> acc@((x, concat type0 (snd(elt)))::tl)
    | h::tl -> aux elt (h::acc) tl

  in match env0 with
    [] -> env1
  | h::t -> envFusion t (aux h [] env1)

(* let test5 = envFusion [('x', Cons(Var('a'), Cons(Var('b'), Empty)));('y', Cons(Var('c'), Empty));] [('x', Cons(Var('c'), Empty))] *)

(* Approximate normal forms *)
type anf = 
  TheEnd
| Omega
| N of n
and n = 
  Lambda of char * n
| L of l
and l =
  Var of char
| App of l * anf

type anf2 = 
  Omega
| Lambda of 

let rec notIn x = function
    TheEnd | Omega -> true
  | N(n) -> niN x n
and niN x = function
    Lambda(c, n) when c = x -> false
  | Lambda(c, n) -> niN x n
  | L(l) -> niL x l
and niL x = function
    Var(c) when x = c -> false
  | Var(c) -> true
  | App(l, a) -> (niL x l)&&(notIn x a)

(* Alpha conversion *)
let rec alpha x y = function
    TheEnd -> assert false
  | Omega -> Omega
  | N(n) -> N(alphaN x y n)
and alphaN x y = function
    Lambda(c, n) when c = x && niN y n-> Lambda(y, alphaN x y n)
  | Lambda(c, n) -> Lambda(c, alphaN x y n)
  | L(l) -> L(alphaL x y l)
and alphaL x y = function
    Var(c) when c = x -> Var(y)
  | Var(c) -> Var(c)
  | App(l, a) -> App(alphaL x y l, alpha x y a)

let tititoto = alpha 'x' 'y'  (N(Lambda('x', L(Var('y')))))

(* Max of two anf *)
let rec compAnf a b = match a, b with
    TheEnd, _ | _, TheEnd -> assert false
  | Omega, _ -> b
  |  _, Omega -> a
  | N(na), N(nb) -> N(compNf na nb)
and compNf a b =  match a, b with
    Lambda(ca, na), Lambda(cb, nb) -> Lambda(ca, compNf na (alphaN cb ca nb))
  | L(la), L(lb) -> L(compLf la lb)
  | _, _ -> failwith "Arg no Least upper bound found !"
and compLf a b = match a, b with
    Var(ca), Var(cb) when ca = cb -> Var(ca)
  | App(la, anfa), App(lb, anfb) -> App((compLf la lb), (compAnf anfa anfb))
  | _, _ -> failwith "Arg no Least upper bound found !"


let tototata = compAnf (N(Lambda('x', L(App(Var('y'), Omega))))) (N(Lambda('z', L(App(Var('y'), N(L(Var('z'))))))))

let rec compAnfs = function
[] -> Omega
  | h::tl -> compAnf (N(h)) (compAnfs tl)



(* Affichage *)
let rec stringOfSType (t : sType) = match t with
    Var(c) -> String.make 1 c
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
      "(" ^ (String.make 1 x) ^ ": " ^ (stringOfMSType type0) ^ ");" ^ aux tl
    else "(" ^ (String.make 1 x) ^ ": " ^ (stringOfMSType type0) ^ ")]"
  in "["^aux e

let rec anfToString  = function
    TheEnd | Omega -> "Omega"
  | N(n) -> nToString n
and nToString = function
  | Lambda(c, n) -> "Lambda ("^String.make 1 c^", "^nToString n^")"
  | L(l) -> lToString l
and lToString = function
    Var(c) -> String.make 1 c
  | App(l, anf) -> "App("^lToString l^", "^anfToString anf^")"

let rec printAnfList = function
    [] -> ()
  | h::tl -> (print_string (nToString h));printAnfList tl





(* Inhabitation algorithm *)
let inhabitation (env: environment) (type0 : sType) =
  let rec t (env: environment) (type0 : sType) (fresh : char list) =

    print_string ("T : " ^ (stringOfEnv env) ^ ", " ^ (stringOfSType type0) ^ "\n");

    match env, type0 with
    (* Si type fleche, alors (abs) s'applique, de plus on doit appliquer (Head) pour chaque extraction possible d'un couple Var / Type de l'environnement *)
      (* ABS *)
      (e, Fleche(type1, type2)) when envIsEmpty e -> abs env fresh type1 type2
      (* ABS + HEAD *)
    | (_::_, Fleche(type1, type2)) -> (abs env fresh type1 type2)@(head env type0 fresh)
      (* HEAD *)
    | (_::_, _) -> head env type0 fresh
    | (_,_) -> []


  and abs (env : environment) fresh (type0 : multisetType) (type1 : sType) = 

    print_string ("ABS : " ^ (stringOfEnv env) ^ ", " ^ (stringOfMSType type0) ^ ", " ^ (stringOfSType type1) ^ "\n");

    (* On prend une variable fraiche et on appelle récursivement t *)
    List.map (fun elt -> Lambda(List.hd fresh, elt)) (t ((List.hd fresh, type0)::env) type1 (List.tl fresh))

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
			 h [fst(extract)] (snd(extract)) (Var(fst(fst(extract)))) type1 type0 fresh) 
	extracts)
    
  and h (env1 : environment) (env2 : environment) (lf : l) (type1 : sType) (type2 : sType) fresh =

    print_string ("H : E1=" ^ (stringOfEnv env1) ^ " E2="^ (stringOfEnv env2)^ " T1=" ^ (stringOfSType type1) ^ " T2=" ^ (stringOfSType type2)^ ", LF="^lToString lf^"\n");

    match env2, type1 with
    (* FINAL + PREFIX *)
      (e, Fleche(typeA, typeS)) when envIsEmpty e -> (final type1 type2 lf)@(prefix env1 env2 lf typeA typeS type2 fresh)
    (* FINAL *)
    | (e, type1) when envIsEmpty e-> final type1 type2 lf
    (* PREFIX *)
    | (_, Fleche(typeA, typeS)) -> prefix env1 env2 lf typeA typeS type2 fresh
    | (_, _) -> []

  and final (type1 : sType) (type2 : sType) (lf : l) =
    print_string ("FINAL : " ^ (stringOfSType type1) ^ ", " ^ 
		     (stringOfSType type2) ^ "--> "^(lToString lf)^"\n");
    if type1 = type2  then [L(lf)] else []

  and prefix (env1 : environment)  (env2 : environment) (lf : l) (type1 : multisetType) (type2 : sType) (type3 : sType) fresh = 
 
    print_string ("PREFIX : " ^ (stringOfEnv env1) ^ ", "^ (stringOfEnv env2)^ ", " ^ (stringOfMSType type1) ^ ", " ^ (stringOfSType type2) ^ ", " ^ (stringOfSType type3)^ "\n");

    let decoupes = envSplitsN 2 env2 in
    (* Pour chaque découpage possible, on cherche les termes que trouve TI puis on appelle h *)
    
    List.concat (List.map (fun (envs : environment list) -> 
	let env20 = (List.hd envs) and env21 = (List.hd (List.tl envs)) in
	
        (* On appelle union, et pour chaque résultat de ti on appelle h *)
	(* UNION *)
	let res = union env20 type1 fresh in (*N(L(Var('m')))*)
	if res != TheEnd then
	h (envFusion env1 env20) env21 (App(lf, res)) type2 type3 fresh
	else []
    )
    decoupes)

  and union (env0 : environment) (type0 : multisetType) fresh = 
    let i = sizeOfMS type0 in
    print_string ("UNION : " ^ (stringOfEnv env0) ^ ", " ^ (stringOfMSType type0) ^ "\n");
    
    if i <= 0 then
      begin
	print_string "Type [], anf: Omega\n";
	Omega
      end
    else
      begin
				(* On cherche toutes les partitions en i elements de l'environment *)
	let partitions = envSplitsN i env0 in
				(* Pour chaque melange et chaque type on tente de touver des termes qui font l'affaire: *)
	let nList = List.concat (List.concat (List.map (fun partition -> 
	  List.map2 (fun partie type0 -> t partie type0 fresh) partition (msToList type0)) partitions)) in
	
	print_string "Anf trouvees: ";printAnfList nList;
	
	print_string "\n";
	if(List.length nList > 0) then (compAnfs nList) else TheEnd
      end
	
  in t env type0 ['x';'y';'z';'p';'q';'r';'s';'t'];;

let toto = inhabitation [] (
  Fleche(
    Cons(
      Fleche(Cons(Var('a'), Empty), Var('a'))
	, Empty), 
    Fleche(Cons(Var('a'), Empty), Var('a'))
  )
)

let tata = inhabitation [] (
    Fleche(
      Cons(
	Fleche(
	Empty,
        Var('a')
	),
	Empty
      ),
      Var('a')
    )
)
