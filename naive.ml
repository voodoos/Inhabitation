(* Simple implementation des multisets *)
type 'a multiset =
  Empty
| Cons of 'a * 'a multiset

let rec msToList = function
    Empty -> []
  | Cons(x, ms) -> Cons(x, Empty)::(msToList ms)

let rec initList = function
      0 -> []
    | m -> []::(initList (m-1))

let rec initMS = function
      0 -> []
    | m -> Empty::(initMS (m-1))

let rec sizeOfMS = function
    Empty -> 0
  | Cons(_, tl) -> 1 + (sizeOfMS tl)

(* Contactenation de deux multiset *)
let rec concat m1 m2 = match m1 with
    Empty -> m2
  | Cons(h, t) -> concat t (Cons(h, m2))

(* Partitions d'un multiset *)
let rec splitsN ms n = 
   let rec add decoupe acc x = match decoupe with 
       [] -> []
     | h::tl -> (acc@(Cons(x, h)::tl))::(add tl (h::acc) x) in

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

let rec envIsEmpty = function
  | [] -> true
  | (_, Empty)::tl -> envIsEmpty tl
  | _ -> false

let rec stringOfType = function
    Empty -> ""
  | Cons(Var(x), ms) -> (String.make 1 x) ^ ";" ^ (stringOfType ms)
  | Cons(Fleche(ms0, ms1), ms2) -> "(" ^ (stringOfType ms0) ^ "->" ^ (stringOfType ms1) ^ ") ;" ^ (stringOfType ms2)

let rec stringOfEnv = function 
    [] -> ""
  | (x, type0)::tl -> "(" ^ (String.make 1 x) ^ ": " ^ (stringOfType type0) ^ ");" ^ stringOfEnv tl

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

let rec anfToString  = function
    TheEnd | Omega -> "Omega"
  | N(n) -> nToString n
and nToString = function
  | Lambda(c, n) -> "Lambda ("^String.make 1 c^", "^nToString n^")"
  | L(l) -> lToString l
and lToString = function
    Var(c) -> String.make 1 c
  | App(l, anf) -> "App("^lToString l^", "^anfToString anf^")"

(* Max of two anf *)
let rec aSupb a b = match b with
    Omega -> true

(* Inhabitation algorithm *)
let inhabitation (env: environment) (type0 : multisetType) =
  let rec t (env: environment) (type0 : multisetType) (fresh : char list) =

    print_string ("T : " ^ (stringOfEnv env) ^ ", " ^ (stringOfType type0) ^ "\n");

    match env, type0 with
    (* Si type fleche, alors (abs) s'applique, de plus on doit appliquer (Head) pour chaque extraction possible d'un couple Var / Type de l'environnement *)
      (* abs *)
      (e, Cons(Fleche(type1, type2), Empty)) when envIsEmpty e -> abs env fresh type1 type2
      (* abs + head *)
    | (_::_, Cons(Fleche(type1, type2), Empty)) -> (abs env fresh type1 type2)@(head env type0 fresh)
      (* head *)
    | (_::_, _) -> head env type0 fresh
    | (_,_) -> []


  and abs env fresh type0 type1 = 

    print_string ("ABS : " ^ (stringOfEnv env) ^ ", " ^ (stringOfType type0) ^ ", " ^ (stringOfType type1) ^ "\n");

    (* On prend une variable fraiche et on appelle récursivement t *)
    List.map (fun elt -> Lambda(List.hd fresh, elt)) (t ((List.hd fresh, type0)::env) type1 (List.tl fresh))

  and head env type0 fresh = 

    print_string ("HEAD : " ^ (stringOfEnv env) ^ ", " ^ (stringOfType type0) ^ "\n");

    (* On regarde toutes les extractions possible d'un couple var / type *)
    let extracts = envExtracts env in

    (* On applique (head) pour chaque extract ( ->  ((x, [type]), envTail) ) *)
    List.concat 
      (List.map 
	 (fun extract -> h [fst(extract)] (snd(extract)) (Var(fst(fst(extract)))) (snd(fst(extract))) type0 fresh) 
	extracts)
    
  and h (env1 : environment) (env2 : environment) (lf : l) type1 type2 fresh =

    print_string ("H : E1=" ^ (stringOfEnv env1) ^ " E2="^ (stringOfEnv env2)^ " T1=" ^ (stringOfType type1) ^ " T2=" ^ (stringOfType type2)^ ", LF="^lToString lf^"\n");

    match env2, type1 with
    (* Final + Prefix *)
      (e, Cons(Fleche(typeA, typeS), Empty)) when envIsEmpty e -> (final type1 type2 lf)@(prefix env1 env2 lf typeA typeS type2 fresh)
    (* Final *)
    | (e, type1) when envIsEmpty e-> final type1 type2 lf
    (* Prefix *)
    | (_, Cons(Fleche(typeA, typeS), Empty)) -> prefix env1 env2 lf typeA typeS type2 fresh
    | (_, _) -> []

  and final type1 type2 lf =
    print_string ("FINAL : " ^ (stringOfType type1) ^ ", " ^ 
		     (stringOfType type2) ^ "--> "^(lToString lf)^"\n");
    if type1 = type2  then [L(lf)] else []

  and prefix (env1 : environment)  (env2 : environment) (lf : l) type1 type2 type3 fresh = 
 
    print_string ("PREFIX : " ^ (stringOfEnv env1) ^ ", "^ (stringOfEnv env2)^ ", " ^ (stringOfType type1) ^ ", " ^ (stringOfType type2) ^ ", " ^ (stringOfType type3)^ "\n");

    let decoupes = envSplitsN 2 env2 in
    (* Pour chaque découpage possible, on cherche les termes que trouve TI puis on appelle h *)
    
    List.concat (List.map (fun (envs : environment list) -> 
	let env20 = (List.hd envs) and env21 = (List.hd (List.tl envs)) in
	
        (* On appelle ti, et pour chaque résultat de ti on appelle h *)
	let res = ti env20 type2 fresh in (*N(L(Var('m')))*)
	
	h (envFusion env1 env20) env21 (App(lf, res)) type2 type3 fresh
    )
    decoupes)

  and ti env0 type0 fresh = let i = sizeOfMS type0 in
		      print_string ("UNION : " ^ (stringOfEnv env0) ^ ", " ^ (stringOfType type0) ^ "\n");

			    if i <= 0 then
			      begin
				print_string "Anf trouvees: Omega";
				Omega
			      end
			    else
			      begin
				(* On cherche toutes les partitions en i elements de l'environment *)
				let partitions = envSplitsN i env0 in
				(* Pour chaque melange et chaque type on tente de touver des termes qui font l'affaire: *)
				let pouet = List.concat (List.concat (List.map (fun partition -> 
				  List.map2 (fun partie type0 -> t partie type0 fresh) partition (msToList type0)) partitions)) in
				
				print_string "Anf trouvees: ";
				let rec p = function
				[] -> ()
				  | h::tl -> (print_string (nToString h));p tl in
				p pouet;
				print_string "\n";
				if(List.length pouet > 0) then (N(List.hd pouet)) else Omega
			      end
						       
  in t env type0 ['x';'y';'z';'p';'q';'r';'s';'t'];;

(*let toto = inhabitation [] (Cons(
  Fleche(
    Cons(
      Fleche(Cons(Var('a'), Empty), Cons(Var('a'), Empty))
	, Empty), 
    Cons(Fleche(Cons(Var('a'), Empty), Cons(Var('a'), Empty))
	   , Empty))
    , Empty))*)

let tata = inhabitation [] (
  Cons(
    Fleche(
      Cons(
	Fleche(
	Empty,
	Cons(Var('a'), Empty)
	),
	Empty
      ),
      Cons(Var('a'), Empty)
    ),
    Empty
  )
)
