(* Simple implementation des multisets *)
type 'a multiset =
  Empty
| Cons of 'a * 'a multiset

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
type sType = 
  Var of char
| Fleche of multisetType * multisetType
and multisetType = sType multiset

type environment = (char * multisetType) list

(* Liste les découpes possibles d'un environnement *)
let rec envSplits = function 
    [] -> [([],[])]
  | (x, tys)::t -> let couples = splits tys and tail = envSplits t in
		   (* On cherche tous les mélanges pour cette variable *)
		   let choix = List.map (fun c -> ((x, fst c),(x, snd c))) couples in
		   (* On les ajoute aux autres mélanges *)
		   List.concat (List.map (fun c -> let (env1, env2) = c in
				      List.map (fun choix -> ((fst choix)::env1, (snd choix)::env2)) choix) tail)

let test2 = envSplits [('x', Cons(Var('a'), Cons(Var('b'), Empty)));('y', Cons(Var('c'), Empty))]


(* Liste les extractions possibles de coupls var /type d'un env *)
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
  let rec t (env: environment) (type0 : multisetType) (fresh : char list) = match env, type0 with
    (* Si type fleche, alors (abs) s'applique, de plus on doit appliquer (Head) pour chaque extraction possible d'un couple Var / Type de l'environnement *)
      (* abs *)
      ([], Cons(Fleche(type1, type2), Empty)) -> abs env fresh type1 type2
      (* abs + head *)
    | (_::_, Cons(Fleche(type1, type2), Empty)) -> (abs env fresh type1 type2)@(head env type0)
      (* head *)
    | (_::_, _) -> head env type0
    | (_,_) -> [TheEnd]


  and abs env fresh type0 type1 = 
    (* On prend une variable fraiche et on appelle récursivement t *)
    t ((List.hd fresh, type0)::env) type1 (List.tl fresh)

  and head env type0 = 
    let extracts = envExtracts env in

    (* On applique (head) pour chaque extract ( ->  ((x, [type]), envTail) ) *)
    List.concat (List.map (fun extract -> h (snd(extract)) [fst(extract)] (N(L(Var(fst(fst(extract)))))) (snd(fst(extract))) type0) extracts)
    
  and h (env1 : environment) (env2 : environment) (anf : anf) type1 type2 = match env2, type1 with
    (* Final + Prefix *)
      ([], Cons(Fleche(typeA, typeS), Empty)) -> (final type1 type2 anf)@(prefix env1 env2 anf typeA typeS type2)
    (* Final *)
    | ([], type1) -> final type1 type2 anf
    (* Prefix *)
    | (_, Cons(Fleche(typeA, typeS), Empty)) -> prefix env1 env2 anf typeA typeS type2
    | (_, _) -> [TheEnd]

  and final type1 type2 anf = if type1 = type2  then [anf] else [TheEnd]

  and prefix env1 env2 (anf : anf) type1 type2 type3 = 
    let envs = envSplits env in
    (* Pour chaque découpage possible, on cherche les termes que trouve TI puis on appelle h *)
    assert false

  and ti = assert false

  and union = assert false
						       
					       
  in t env type0 ['x';'y';'z';'p';'q';'r';'s';'t']
