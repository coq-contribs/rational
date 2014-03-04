

open Frame;;


(*     SIMPLIFICATION EN T^ETE DANS UN tree    


L'algorithme:
-------------
Avec les m^emes notations que pr'ec'edemment:
 Notations : t1 = [a1;a2;a3....;an] (les tree sont isomorphes `a des listes)
             t2 = [b1;b2;b3;...;bn]

Etape 1: on compare a1 `a b1 puis a2 `a b1 .....
^^^^^^^  Si on trouve ai correspondant `a b1, on rend la suite de tactique
  qui permet de faire remonter ai en t^ete de t1.
        Sinon 'etape i=1 +1

Etape i+1: Recommencer avec bi+1 en oubliant pas de noter la permutation
^^^^^^^^^ bi bi+1.

On rend donc deux listes de tactiques, la premi`ere devant agir sur
t1 la seconde sur t2.
L'esprit et de mettre en t^ete des listes deux 'el'ements identiques

Cas particulier important: si une des deux listes est vide, il faut mettre
l'element neutre `a la place donc exiger son existence
 *)


exception No_common_head;;
exception Not_equal;;

let cOMMON_HEAD_SEARCH_without_neutral =

let rec find_b1_in_t1 b1 = 
  let rec fix ll = function
      Node(x,Leaf(a1),r1) -> 
            if a1 = b1 then ll,r1
                       else fix (a1::ll) r1
    | Leaf(a_end) -> if a_end = b1 then ll,Bottom
                                   else raise Not_equal
    | _   -> raise Not_normalized
  in fix []

(* find_b1_in_t1 b t cherche b dans t et
       # Si il ne trouve pas b -> exception Not_normalized
       # Si il trouve b rend [a1..ai-1],[ai+1,..an]
(avec t=[a1....an])      *)


in

let aux x b term l_ai =
   let rec fix term tac_list = function
      []      -> Node(x,Leaf(b),term),List.rev(tac_list)
    | a::rest -> if term = Bottom then
 fix (Leaf a) ((COM(Leaf a,Leaf b),List.rev rest)::tac_list) rest
                                 else
   fix (Node(x,Leaf(a),term)) 
        ((PERMUT((Leaf a),(Leaf b),term),List.rev rest)::tac_list) rest
   in fix term [] l_ai

(* aux op b term [a1...ap] construit la liste de tactiques
qui permet de passer de [a1..ap,b,term] `a [b,a1...ap,term] *)

in

let rec search_head op t1 t2 = function 
   (* filtrage sur t2, l2 liste des membres de t2 d'ej`a examin'es *)
         Node(x,Leaf(b1),r2) ->
   (try 
       ( let ll1,term1 = find_b1_in_t1 b1 t1 in
         let ll2,term2 = find_b1_in_t1 b1 t2 in
         let ltac1 = snd(aux op b1 term1 ll1) in
         let ltac2 = snd(aux op b1 term2 ll2) in
          (ltac1,ltac2))
   with
         e when Errors.noncritical e -> search_head op t1 t2 r2)
  
       | Leaf(b1) ->

  (try 
       ( let ll1,term1 = find_b1_in_t1 b1 t1 in
         let ll2,term2 = find_b1_in_t1 b1 t2 in
         let ltac1 = snd(aux op b1 term1 ll1) in
         let ltac2 = snd(aux op b1 term2 ll2) in
          (ltac1,ltac2))
   with
         e when Errors.noncritical e -> raise No_common_head)


       | _ -> raise Not_normalized

in 
  function (op,t1,t2) ->

search_head op t1 t2 t2;;

exception Do_nothing;;

let case_neutral b (t1,t2) (l1,l2) =
          if b = true then ((((EXPAND(t1,t2)),[])::l1),l2)
                      else (l1,(((EXPAND(t1,t2)),[])::l2));;



let cOMMON_HEAD_SEARCH = function  (op,t1,t2,n) ->
 match (t1,t2) with
    (Leaf(a),Leaf(b))-> raise Do_nothing
   |(Leaf(a),t) -> if a=n then raise Do_nothing
                          else
     case_neutral true (t1,t2)
      (cOMMON_HEAD_SEARCH_without_neutral (op,(Node(op,t1,Leaf(n))),t2))
   |(t,Leaf(b)) -> if b=n then raise Do_nothing
                          else
     case_neutral false (t1,t2)
      (cOMMON_HEAD_SEARCH_without_neutral (op,t1,Node(op,t2,Leaf(n))))
   | _-> cOMMON_HEAD_SEARCH_without_neutral (op,t1,t2);;

     