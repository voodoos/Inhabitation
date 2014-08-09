(* Simple implementation des multisets *)
type 'a multiset =
  Empty
| Cons of 'a * 'a multiset

let rec initList = function
      0 -> []
    | m -> []::(initList (m-1))

let rec initMS = function
      0 -> []
    | m -> Empty::(initMS (m-1))

(* Contactenation de deux multiset *)
let rec concat m1 m2 = match m1 with
    Empty -> m2
  | Cons(h, t) -> concat t (Cons(h, m2))


(* Liste les découpes possibles d'un multiset *)
let rec splits = function
    Empty -> [(Empty,Empty)]
  | Cons(h, t) -> let r = splits t in
	    List.map (fun e -> (Cons(h, fst e), snd e)) r
	      @ List.map (fun e -> (fst e, Cons(h, snd e))) r

let test1 = splits (Cons('a', Cons('b', Empty)))

let rec splitsN ms n = 
   let rec add decoupe acc x = match decoupe with 
       [] -> []
     | h::tl -> (acc@(Cons(x, h)::tl))::(add tl (h::acc) x) in
     (*| h::tl -> (acc@((x::h)::tl))::(add tl (h::acc) x) in*)

  match ms with
    Empty -> [initMS n] (* [[ [];[];[];...;[] ]] *)
  | Cons(h, tl) -> let reste = (splitsN tl n) in
	     List.concat (List.map (fun d -> (add d [] h)) reste)

let test0 = splitsN (Cons(1, Cons(2, Empty))) 3


(* Liste les extractions possibles d'un multiset *)
let extracts l =
  let rec aux acc = function
  Empty -> []
  | Cons(h, t) -> (h, concat acc t)::(aux (Cons(h, acc)) t) in
  aux Empty l

let test3 = extracts (Cons(1, Cons(2, Cons(3, Cons(4, Empty)))))



(* Grammaire pour les patterns, les termes et les contextes *)
type term = 
  Var of char
| Lambda of char * term 
| App of term * term

type context = 
  Blank 
| CLambda of char * context 
| AppLeft of context * term
| AppRight of term * context

(* Opération de passage au contexte *)
let rec contextualize c t = match c with
    Blank -> t
  | CLambda(x, c2) -> Lambda(x, contextualize c2 t)
  | AppLeft(c2, t2) -> App(contextualize c2 t, t2)
  | AppRight(t2, c2) -> App(t2, contextualize c2 t)

(* Types *)
type multisetType = sType multiset
and sType = 
  Var of char
| Fleche of multisetType * multisetType

type environment = (char * multisetType) list

let rec stringOfType = function
    Empty -> ""
  | Cons(Var(x), ms) -> (String.make 1 x) ^ ";" ^ (stringOfType ms)
  | Cons(Fleche(ms0, ms1), ms2) -> "(" ^ (stringOfType ms0) ^ "->" ^ (stringOfType ms1) ^ ") ;" ^ (stringOfType ms2)

let rec stringOfEnv = function 
    [] -> ""
  | (x, type0)::tl -> "(" ^ (String.make 1 x) ^ ": " ^ (stringOfType type0) ^ ");" ^ stringOfEnv tl

(* Liste les découpes possibles d'un environnement *)
let rec envSplits = function 
    [] -> [([],[])]
  | (x, tys)::t -> let couples = splits tys and tail = envSplits t in
		   (* On cherche tous les mélanges pour cette variable *)
		   let choix = List.map (fun c -> ((x, fst c),(x, snd c))) couples in
		   (* On les ajoute aux autres mélanges *)
		   List.concat (List.map (fun c -> let (env1, env2) = c in
				      List.map (fun choix -> ((fst choix)::env1, (snd choix)::env2)) choix) tail)

let test2 = envSplits [('x', Cons(Var('a'), Cons(Var('b'), Empty)));('y', Cons(Var('c'), Cons(Var('d'), Empty)))]

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
		    
let test22 = envSplitsN 3 [('x', Cons(Var('a'), Cons(Var('b'), Empty)));('y', Cons(Var('c'), Empty))]


(* Liste les extractions possibles de couples var /type d'un env *)
let envExtracts (env : environment) = 
  let rec aux acc = function
    [] -> []
  | (x, types)::t -> let extracts = extracts types in
		   List.map (fun ex -> let (e, tail) = ex in let elt = Cons(e, Empty) in match tail with
		     Empty -> ((x, elt), t@acc)
		   | _ -> ((x, elt), (x, tail)::t@acc)) extracts
		     @ (aux ((x, types)::acc) t) in
  aux [] env

let test4 = envExtracts [('x', Cons(Var('a'), Cons(Var('b'), Empty)));('y', Cons(Var('c'), Empty));]

(* Fusionne deux environnements *)
let rec envFusion (env0 : environment) (env1 : environment) = 
  let rec aux elt acc = function 
      [] -> elt::acc
    | (x, type0)::tl when x = fst(elt) -> acc@((x, concat type0 (snd(elt)))::tl)
    | h::tl -> aux elt (h::acc) tl

  in match env0 with
    [] -> env1
  | h::t -> envFusion t (aux h [] env1)

let test5 = envFusion [('x', Cons(Var('a'), Cons(Var('b'), Empty)));('y', Cons(Var('c'), Empty));] [('x', Cons(Var('c'), Empty))]

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


(* Inhabitation algorithm *)
let inhabitation (env: environment) (type0 : multisetType) =
  let rec t (env: environment) (type0 : multisetType) (fresh : char list) =

    print_string ("T : " ^ (stringOfEnv env) ^ ", " ^ (stringOfType type0) ^ "\n");

    match env, type0 with
    (* Si type fleche, alors (abs) s'applique, de plus on doit appliquer (Head) pour chaque extraction possible d'un couple Var / Type de l'environnement *)
      (* abs *)
      ([], Cons(Fleche(type1, type2), Empty)) -> abs env fresh type1 type2
      (* abs + head *)
    | (_::_, Cons(Fleche(type1, type2), Empty)) -> (abs env fresh type1 type2)@(head env type0)
      (* head *)
    | (_::_, _) -> head env type0
    | (_,_) -> []


  and abs env fresh type0 type1 = 
    print_string ("ABS : " ^ (stringOfEnv env) ^ ", " ^ (stringOfType type0) ^ ", " ^ (stringOfType type1) ^ "\n");
    (* On prend une variable fraiche et on appelle récursivement t *)
    List.map (fun elt -> Lambda(List.hd fresh, elt)) (t ((List.hd fresh, type0)::env) type1 (List.tl fresh))

  and head env type0 = 
    print_string ("HEAD : " ^ (stringOfEnv env) ^ ", " ^ (stringOfType type0) ^ "\n");
    (* On regarde toutes les extractions possible d'un couple var / type *)
    let extracts = envExtracts env in

    (* On applique (head) pour chaque extract ( ->  ((x, [type]), envTail) ) *)
    List.concat 
      (List.map 
	 (fun extract -> h [fst(extract)] (snd(extract)) (Var(fst(fst(extract)))) (snd(fst(extract))) type0) 
	extracts)
    
  and h (env1 : environment) (env2 : environment) (lf : l) type1 type2 =
    print_string ("H : " ^ (stringOfEnv env1) ^ ", "^ (stringOfEnv env2)^ ", " ^ (stringOfType type1) ^ ", " ^ (stringOfType type2)^ "\n");

    match env2, type1 with
    (* Final + Prefix *)
      ([], Cons(Fleche(typeA, typeS), Empty)) -> (final type1 type2 lf)@(prefix env1 env2 lf typeA typeS type2)
    (* Final *)
    | ([], type1) -> final type1 type2 lf
    (* Prefix *)
    | (_, Cons(Fleche(typeA, typeS), Empty)) -> prefix env1 env2 lf typeA typeS type2
    | (_, _) -> []

  and final type1 type2 lf =
    print_string ("FINAL : " ^ (stringOfType type1) ^ ", " ^ (stringOfType type2) ^ "\n");
    if type1 = type2  then [L(lf)] else []

  and prefix (env1 : environment)  (env2 : environment) (lf : l) type1 type2 type3 = 
    print_string ("PREFIX : " ^ (stringOfEnv env1) ^ ", "^ (stringOfEnv env2)^ ", " ^ (stringOfType type1) ^ ", " ^ (stringOfType type2) ^ ", " ^ (stringOfType type3)^ "\n");
    let decoupes = envSplitsN 2 env2 in
    (* Pour chaque découpage possible, on cherche les termes que trouve TI puis on appelle h *)
    
    List.concat (List.map (fun (envs : environment list) -> 
	let env20 = (List.hd envs) and env21 = (List.hd (List.tl envs)) in
	
        (* On appelle ti, et pour chaque résultat de ti on appelle h *)
	let res = N(L(Var('m'))) in (*ti env20 type2 in*)

	h (envFusion env1 env20) env21 (App(lf, res)) type2 type3) decoupes)

  and ti = []

  and union = []
						       
  in t env type0 ['x';'y';'z';'p';'q';'r';'s';'t'];;

let toto = inhabitation [] (Cons(
  Fleche(
    Cons(
      Fleche(Cons(Var('a'), Empty), Cons(Var('a'), Empty))
	, Empty), 
    Cons(Fleche(Cons(Var('a'), Empty), Cons(Var('a'), Empty))
	   , Empty))
    , Empty))

