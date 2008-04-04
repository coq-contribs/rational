
type ('a,'b) tree = Bottom
                  | Leaf of 'a 
                  | Node of 'b * ('a,'b) tree * ('a,'b) tree;;

type lAW = Com | Assoc | Assoc_inv | Permut;;

type ('a,'b) tACTIC = 
          COM of ('a,'b) tree * ('a,'b) tree
        | ASSOC of ('a,'b)tree * ('a,'b) tree * ('a,'b) tree
        | ASSOC_inv of ('a,'b)tree * ('a,'b) tree * ('a,'b) tree
        | PERMUT of  ('a,'b)tree * ('a,'b) tree * ('a,'b) tree 
        | EXPAND of  ('a,'b)tree * ('a,'b) tree;;
(*

exception FORBID of LAW;;

let C = function node(x,left,right) ->
                   node(x,right,left),COM(left,right)
                | _ -> raise (FORBID Com) ;;

(* associativit'e *)

let A = function 
         node(x,left,node(y,left_son,right_son)) ->
          node(x,node(y,left,left_son),right_son),
                        ASSOC(left,left_son,right_son)
             | _ -> raise (FORBID Assoc);;

(* associativit'e dans l'autre sens *)

let A_inv = function 
                 node(x,node(y,left,left_son),right_son) ->   
                     node(x,left,node(y,left_son,right_son)),
                        ASSOC_inv(left,left_son,right_son)
                | _ ->  raise (FORBID Assoc_inv);;

let P = function 
              node(x,left,node(y,left_son,right_son)) ->
                  node(x,left_son,node(y,left,right_son)),
                        PERMUT(left,left_son,right_son)
                | _ -> raise (FORBID Permut);;



(* La normalisation consiste \`a rendre l'arbre lin'eaire: tous
les fils gauches sont des feuilles 
NORMALIZE rend une suites de tactiques ainsi que le nouvel arbre
On utilise donc un point fixe compos'e d'une liste de tactiques
et d'un arbre \`a transformer. On utilise un mutable pour
stocker les tactiques*)


let NORMALIZE = function t ->
  let tac_list = ref([]) in
  let rec aux = function
          node(x,left,right) ->
          (match left with leaf(_) -> node(x,left,(aux right))
                        | node(y,lleft,lright)->
  tac_list := ASSOC_inv(lleft,lright,right):: !tac_list ;
                  aux (node(x,lleft,node(y,lright,right))))   
          | x -> x
in let norm_t = aux(t) 
   in rev(!tac_list),norm_t
;;
*)
exception Not_normalized;;

let perm_first b r =
match r with 
   Node(x,Leaf(a1),r1) -> PERMUT(Leaf b,Leaf a1,r1)
  |Leaf(a1) -> COM(Leaf b, Leaf a1)
  | _ -> raise Not_normalized
;;

let rec cons_tree x t = function
      [] -> t
    | a::rest -> cons_tree x (Node(x,Leaf a,t)) rest
;;
