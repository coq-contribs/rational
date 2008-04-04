
(*  EGALIT'E MODULO PERMUTATION DANS UN tree


On calcule ici la pernutation qui permet d'identifier deux
arbres normalis'es, on se contente ici de rendre la suite
de tactiques qui reussie:
L'algorithme est le suivant:
On prend deux tree t1 et t2 et on ne pratique des permutations que sur
le premier des deux:
 Notations : t1 = [a1;a2;a3....;an] (les tree sont isomorphes `a des listes)
             t2 = [b1;b2;b3;...;bn]

Etape 1: On recherche la premi`ere occurence de b1 dans t1:
c'est ce que fait find_b1_in_t1 qui prend en arguments b1 et t2 et rend
le couple [a1;a2;..;ap-1] [ap+1;....an] sachant que ap= b1
(*si il y echec, bien sur t1 et t2 ne sont pas convertibles *)

Etape 2 :
     Si [a1;a2;...ap-1] \= [] alors

On fait remonter bi en t^ete de t1 avec des permutations:
       perm ap-1 b [ap+1.....an]
       perm ap-2 b [ap-1,ap+1,...an]
              .
              .
       perm a1 b [a2...........an]
`a la fin, l'etat de (t1,t2) est donc
       ([b1;a1;....;ap-1;ap+1;...an];[b1;b2;....;bn]

     Si [a1;a2...ap-1] = [] <=> a1=b1
             RIEN

Etape 3: On it`ere Etape1;Etape2 en diminuant d'un 'el'ement la taille des
deux listes `a chaque etape.
*)

open Struct;;

exception Not_equal;;


let iDENTIFY = 

let rec find_b1_in_t1 b1 = 
  let rec fix ll = function
      Node(x,Leaf(a1),r1) -> 
            if a1 = b1 then ll,r1
                       else fix (a1::ll) r1
    | Leaf(a_end) -> if a_end = b1 then ll,Bottom
                                   else raise Not_equal
    | _   -> raise Not_normalized
  in fix []
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
in

let rec identify = function x,t1,t2 ->
 match t1,t2 with
   Node(x,(Leaf a1),r1),Node(y,(Leaf b1),r2) as t ->
    if a1 = b1 then List.map (fun (tac,ll)->(tac,a1::ll)) (identify (x,r1,r2)) else
      let l_ai,term = find_b1_in_t1 b1 (fst t)
      in
       let (new_t1,tac_list) = aux x b1 term l_ai 
       in tac_list @ identify (x,new_t1,snd t)
 | Leaf(a1),Leaf(b1) -> if a1=b1 then [] else raise Not_equal
 | _ -> raise Not_normalized
 
in identify
;;