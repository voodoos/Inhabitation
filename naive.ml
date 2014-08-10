(* Simple implementation des multisets *)
type 'a multiset =
  Empty
| Cons of 'a * 'a multiset

let rec msToList = function
    Empty -> []
  | Cons(x, ms) -> x::(msToList ms)

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
| Fleche of multisetType * sType

type environment = (char * multisetType) list

let rec envIsEmpty = function
  | [] -> true
  | (_, Empty)::tl -> envIsEmpty tl
  | _ -> false

let rec stringOfSType = function
    Var(c) -> String.make 1 c
  | Fleche(ms, s) -> (stringOfMSType ms)^" -> "^stringOfSType s
and stringOfMSType ms = 
  let rec aux = function
    Empty -> ""
  | Cons(s, ms) -> stringOfSType s ^ ";" ^ (stringOfMSType ms)
  in "["^aux ms^"]"


let rec stringOfEnv = function 
    [] -> ""
  | (x, type0)::tl -> "(" ^ (String.make 1 x) ^ ": " ^ (stringOfMSType type0) ^ ");" ^ stringOfEnv tl

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
let inhabitation (env: environment) (type0 : sType) =
  let rec t (env: environment) (type0 : sType) (fresh : char list) =

    print_string ("T : " ^ (stringOfEnv env) ^ ", " ^ (stringOfSType type0) ^ "\n");

    match env, type0 with
    (* Si type fleche, alors (abs) s'applique, de plus on doit appliquer (Head) pour chaque extraction possible d'un couple Var / Type de l'environnement *)
      (* abs *)
      (e, Fleche(type1, type2)) when envIsEmpty e -> abs env fresh type1 type2
      (* abs + head *)
    | (_::_, Fleche(type1, type2)) -> (abs env fresh type1 type2)@(head env type0 fresh)
      (* head *)
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
    (* Final + Prefix *)
      (e, Fleche(typeA, typeS)) when envIsEmpty e -> (final type1 type2 lf)@(prefix env1 env2 lf typeA typeS type2 fresh)
    (* Final *)
    | (e, type1) when envIsEmpty e-> final type1 type2 lf
    (* Prefix *)
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
	
        (* On appelle ti, et pour chaque résultat de ti on appelle h *)
	let res = ti env20 type1 fresh in (*N(L(Var('m')))*)
	
	h (envFusion env1 env20) env21 (App(lf, res)) type2 type3 fresh
    )
    decoupes)

  and ti (env0 : environment) (type0 : multisetType) fresh = let i = sizeOfMS type0 in
		      print_string ("UNION : " ^ (stringOfEnv env0) ^ ", " ^ (stringOfMSType type0) ^ "\n");

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
