(* Tools *)

let max (x, y) = match x with a when a > y -> a | _ -> y

let rec test_unit (name, f, value, result) =
  match (value, result) with
  | hd :: [], hd2 :: [] when f hd = hd2 ->
      print_endline ("[" ^ name ^ "] : OK\n")
  | hd :: tl, hd2 :: tl2 when f hd = hd2 -> test_unit (name, f, tl, tl2)
  | _ -> print_endline ("[" ^ name ^ "] : **KO**\n")

(* Type declaration *)

exception Ooc of string

type prop =
  | Symb of string
  | Top
  | Bot
  | Not of prop
  | And of prop * prop
  | Or of prop * prop
  | Imp of prop * prop
  | Equ of prop * prop

type valVerite = Zero | Un
type interpretation = (string * valVerite) list

(* 1 - Syntaxe de la logique propositionnelle *)

(* Q1 *)
let f_1 = Equ (And (Symb "a", Symb "b"), Or (Not (Symb "a"), Symb "b"))
let f_2 = Or (Not (And (Symb "a", Symb "b")), Not (Imp (Symb "a", Symb "b")))

let f_3 =
  And
    ( Not (Imp (Symb "a", Or (Symb "a", Symb "b"))),
      Not (Not (And (Symb "a", Or (Symb "b", Not (Symb "c"))))) )

let f_4 =
  And
    ( Or (Not (Symb "a"), Or (Symb "b", Symb "d")),
      And
        ( Or (Not (Symb "d"), Symb "c"),
          And
            ( Or (Symb "c", Symb "a"),
              And
                ( Or (Not (Symb "c"), Symb "d"),
                  Or (Not (Symb "c"), Not (Symb "b")) ) ) ) )

(* Q2 *)
let rec nbc f =
  match f with
  | Symb _ | Top | Bot -> 0
  | Not a -> 1 + nbc a
  | And (a, b) | Or (a, b) | Imp (a, b) | Equ (a, b) -> 1 + nbc a + nbc b

(* Q3 *)

(*
  function prof
  @param f : {prop} une fbf
  @returns {int} profondeur de la fbf
*)

let rec prof f =
  match f with
  | Symb _ | Top | Bot -> 0
  | Not a -> 1 + nbc a
  | And (a, b) | Or (a, b) | Imp (a, b) | Equ (a, b) -> 1 + max (nbc a, nbc b)

(* Q4 *)

(*
  function sp
  @param f : {prop} une fbf
  @returns {string list} liste de tout les symboles
*)

let rec ajouteSiAbsent (li, e) =
  match li with
  | [] -> [ e ]
  | hd :: tl when hd = e -> hd :: tl
  | hd :: tl -> [ hd ] @ ajouteSiAbsent (tl, e)

let rec union (l, li) =
  match li with [] -> l | hd :: tl -> union (ajouteSiAbsent (l, hd), tl)

let sp f =
  let rec res f =
    match f with
    | Symb a -> [ a ]
    | Not a -> res a
    | And (a, b) | Or (a, b) | Imp (a, b) | Equ (a, b) -> union (res a, res b)
    | Bot | Top -> []
  in
  List.sort String.compare (res f)

(* Q5 *)
let rec affiche f =
  match f with
  | Symb a -> a
  | Bot -> "Bot"
  | Top -> "Top"
  | Not a -> "Not(" ^ affiche a ^ ")"
  | And (a, b) -> "(" ^ affiche a ^ " ^ " ^ affiche b ^ ")"
  | Or (a, b) -> "(" ^ affiche a ^ " v " ^ affiche b ^ ")"
  | Imp (a, b) -> "(" ^ affiche a ^ " => " ^ affiche b ^ ")"
  | Equ (a, b) -> "(" ^ affiche a ^ " <=> " ^ affiche b ^ ")"

(** Q6 **)
let rec affichePri (f : prop) =
  match f with
  | Symb _ | Bot | Top -> affiche f
  | Not a -> (
      match a with
      | Symb _ | Bot | Top | Not _ -> "Not " ^ affichePri a
      | _ -> "Not (" ^ affichePri a ^ ")")
  | And (a, b) -> (
      match (a, b) with
      | _, Imp _ | _, Equ _ -> affichePri a ^ " ^ (" ^ affichePri b ^ ")"
      | Imp _, _ | Equ _, _ -> "(" ^ affichePri a ^ ") ^ " ^ affichePri b
      | _, _ -> affichePri a ^ " ^ " ^ affichePri b)
  | Or (a, b) -> (
      match (a, b) with
      | _, Imp _ | _, Equ _ -> affichePri a ^ " v (" ^ affichePri b ^ ")"
      | Imp _, _ | Equ _, _ -> "(" ^ affichePri a ^ ") v " ^ affichePri b
      | _, _ -> affichePri a ^ " v " ^ affichePri b)
  | Imp (a, b) -> (
      match (a, b) with
      | Equ _, _ -> "(" ^ affichePri a ^ ") => " ^ affichePri b
      | _, _ -> affichePri a ^ " => " ^ affichePri b)
  | Equ (a, b) -> affichePri a ^ " <=> " ^ affichePri b
;;

print_endline (affiche f_1);;
print_endline (affichePri f_1 ^ "\n");;

print_endline
  (affichePri (Equ (Or (Symb "a", Imp (Symb "a", Symb "b")), Symb "c")) ^ "\n")
;;

print_endline
  (affichePri (Imp (Or (Symb "a", Equ (Symb "a", Symb "b")), Symb "c")) ^ "\n")
;;

print_endline (affichePri (Imp (Equ (Symb "a", Symb "b"), Symb "b")) ^ "\n");;
print_endline (affiche f_2);;
print_endline (affichePri f_2 ^ "\n");;
print_endline (affiche f_3);;
print_endline (affichePri f_3 ^ "\n");;
print_endline (affiche f_4);;
print_endline (affichePri f_4 ^ "\n")

(* 2 - Sémantique des propositions *)

(* Q7 *)
let i_1 = [ ("a", Un); ("b", Zero); ("c", Un) ]
let i_2 = [ ("a", Zero); ("b", Zero); ("c", Zero) ]
let i_3 = [ ("a", Un); ("b", Un); ("c", Un) ]

(*
   function int^*(args)
   @returns {valVerite} revoit la valeur de vérité associé à un connecteur logique
*)

(* Q8 *)

let rec intSymb (v, (i : interpretation)) =
  match i with
  | [] -> Zero
  | (a, b) :: _ when a = v -> b
  | (a, b) :: f when a != v -> intSymb (v, f)
  | _ -> raise (Ooc "v not in i")

(* Q9 *)

let intNeg = function Zero -> Un | Un -> Zero
let intAnd = function Un, Un -> Un | _ -> Zero
let intOr = function Zero, Zero -> Zero | _ -> Un
let intImp = function Un, Zero -> Zero | _ -> Un

let intEqu ((a : valVerite), (b : valVerite)) =
  match a with a when a = b -> Un | _ -> Zero

let intTop = Un
let intBot = Zero

(* Q10 *)
let rec valV (f, i) =
  match f with
  | Symb a -> intSymb (a, i)
  | Top -> intTop
  | Bot -> intBot
  | Not a -> intNeg (valV (a, i))
  | And (a, b) -> intAnd (valV (a, i), valV (b, i))
  | Or (a, b) -> intOr (valV (a, i), valV (b, i))
  | Equ (a, b) -> intEqu (valV (a, i), valV (b, i))
  | Imp (a, b) -> intImp (valV (a, i), valV (b, i))

(* Q11 *)
let modele (f, inter) =
  match f with a when valV (a, inter) = Un -> true | _ -> false

(* 3 - Satisfiabilité et validité d’une proposition *)

(* Q12 *)
let o_1 : interpretation list =
  [
    [ ("q", Un); ("p", Un) ];
    [ ("q", Un); ("p", Zero) ];
    [ ("q", Zero); ("p", Un) ];
    [ ("q", Zero); ("p", Zero) ];
  ]

(* Q13 *)
let rec consTous (e, l) =
  match l with
  | [] -> []
  | [ [] ] -> [ [ e ] ]
  | hd :: tl -> [ [ e ] @ hd ] @ consTous (e, tl)

let rec ensInt (l : string list) : interpretation list =
  match l with
  | [] -> [ [] ]
  | [ e ] -> [ [ (e, Zero) ]; [ (e, Un) ] ]
  | hd :: tl ->
      union (consTous ((hd, Un), ensInt tl), consTous ((hd, Zero), ensInt tl))

(* Q14 *)
let rec existeModele (f, (li : interpretation list)) =
  match li with
  | [] -> false
  | hd :: _ when modele (f, hd) -> true
  | _ :: tl -> existeModele (f, tl)

let satisfiable f = existeModele (f, ensInt (sp f))

(* Q15 *)
let rec tousModele (f, (li : interpretation list)) =
  match li with
  | [] -> true
  | hd :: tl when modele (f, hd) -> tousModele (f, tl)
  | _ :: tl -> false

let valide f = tousModele (f, ensInt (sp f))

(* Q16 *)
let insatisfiable f = not (satisfiable f)

(* 4 -  Equivalence et conséquence logique *)

(* Q17 *)

let rec memesModeles (f, g, ensIntfg) =
  match ensIntfg with
  | [] -> true
  | hd :: tl when modele (f, hd) = modele (g, hd) -> memesModeles (f, g, tl)
  | _ -> false

let equivalent1 (f, g) = memesModeles (f, g, ensInt (union (sp f, sp g)))
let equivalent2 (f, g) = valide (Equ (f, g))
let test = And (Or (Symb "a", Symb "b"), Symb "c")
let test2 = Or (And (Symb "a", Symb "c"), And (Symb "c", Symb "b"))
let test3 = Or (Or (Symb "a", Symb "b"), Not (Symb "a"))
let test4 = Not (And (And (Symb "c", Symb "d"), Not (Symb "c")))

(* Q18 *)

let rec list_des_valide (f, i) =
  match i with
  | [] -> []
  | hd :: tl when modele (f, hd) -> [ hd ] @ list_des_valide (f, tl)
  | _ :: tl -> list_des_valide (f, tl)

let consequence2 (h, c) =
  match c with
  | f when tousModele (f, list_des_valide (h, ensInt (sp h))) -> true
  | _ -> false

let testc1 = Symb "a"
let testc2 = Or (Symb "a", Symb "b")
let testc3 = And (Symb "a", Symb "b")
let testc4 = Or (Or (Symb "a", Symb "b"), Not (Symb "a"))
let testc5 = Not (And (And (Symb "c", Symb "d"), Not (Symb "c")))
let testc6 = And (And (Symb "a", Symb "b"), Not (Symb "a"))
let testc7 = Or (Symb "c", Symb "d")

(* Q19 *)

let tousSP l =
  let rec res = function [] -> [] | hd :: tl -> union (sp hd, res tl) in
  List.sort String.compare (res l)

(* Q20 *)

let rec modeleCommun (i, lfbf) =
  match lfbf with
  | [] -> true
  | hd :: tl when modele (hd, i) -> modeleCommun (i, tl)
  | _ -> false

(* Q21 *)

let rec conjonction = function [] -> Top | hd :: tl -> And (hd, conjonction tl)

let contradictoire = function
  | [] -> false
  | li -> insatisfiable (conjonction li)

(* Q22 *)

let consequence (li, f) = consequence2 (conjonction li, f)
let testc_21 = And (Symb "a", Symb "b")
let testc_22 = Not (Symb "a")
let testc_23 = Imp (Symb "b", Symb "d")
let testc_24 = Imp (Symb "c", Symb "d")

(* Q23 *)

(* 4 - Q23: consequenceV *)

let consequenceV (li, f) = valide (Or (Not f, conjonction li))

(* 4 - Q24: consequenceI *)

let consequenceI (li, f) = insatisfiable (And (f, Not (conjonction li)));;

(* Test Unitaire *)

print_endline "[*********** Test Unitaire ***********]\n";;
test_unit ("nbc", nbc, [ f_1; f_2; f_3; f_4 ], [ 4; 5; 9; 15 ]);;

test_unit
  ( "sp",
    sp,
    [ f_1; f_2; f_3; f_4 ],
    [ [ "a"; "b" ]; [ "a"; "b" ]; [ "a"; "b"; "c" ]; [ "a"; "b"; "c"; "d" ] ] )
;;

test_unit
  ( "statisfiable",
    satisfiable,
    [
      Symb "a";
      Not (Symb "a");
      And (Symb "a", Symb "b");
      Or (Or (Symb "a", Symb "b"), Not (Symb "a"));
      f_1;
      f_2;
      f_3;
      f_4;
    ],
    [ true; true; true; true; true; true; false; true ] )
;;

test_unit
  ( "equivalent",
    equivalent1,
    [ (Symb "a", Not (Symb "a")); (test, test2); (test3, test4) ],
    [ false; true; true ] )
;;

test_unit
  ( "equivalent2",
    equivalent2,
    [ (Symb "a", Not (Symb "a")); (test, test2); (test3, test4) ],
    [ false; true; true ] )
;;

test_unit
  ( "consequence2",
    consequence2,
    [ (testc1, testc2); (testc1, testc3); (testc4, testc5); (testc6, testc7) ],
    [ true; false; true; true ] )
;;

test_unit
  ("tousSP", tousSP, [ [ f_1; f_2; f_3; f_4 ] ], [ [ "a"; "b"; "c"; "d" ] ])
;;

test_unit
  ( "consequence",
    consequence,
    [ ([ testc_21; testc_22; testc_23 ], testc_24) ],
    [ true ] )
;;

print_endline "[*************************************]"
