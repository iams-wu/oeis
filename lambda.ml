(*

lambda rooted skeletons -- big schroeder numbers
oeis.org/A006318

little schroeder numbers
oeis.org/A001003

any rooted terms (grygiel/lescanne)
oeis.org/A220894

lambda rooted terms
oeis.org/A220895

any rooted terms (tromp)
oeis.org/A195691

C n k
oeis.org/a091894

C n
oeis.org/a000108

 *)
type leaf =
  | Place
  | X of int

type calculus =
  | L of int * calculus
  | A of calculus * calculus
  | F of leaf
;;
  
module IMap = Map.Make(String) ;;
let emptymap = IMap.empty ;;


let find_or k map elsedo =
  match IMap.mem k map with
  | true -> IMap.find k map
  | false -> elsedo ()
;;

let rec repeat x n =
  match n <= 0 with
  | true -> []
  | false -> x :: repeat x (n-1)
;;

let cat delim list =
  let rec cat xs =
    match xs with
    | [] -> ""
    | x :: [] -> x
    | x :: xs -> x ^ delim ^ cat xs
  in
  cat list
;;

let rec stringof chars =
  match chars with
    | c :: chars ->
      (Char.escaped c) ^ stringof chars
    | [] -> ""    
;;
  
let rec lchr term =
  match term with
  | L ( i , sub ) -> "l" ^ lchr sub
     
  | A ( left , right ) -> "a" ^ lchr left ^ lchr right

  | F ( Place ) -> "~"
                                                 
  | F ( X i ) -> ('~' :: '|' :: repeat '|' i) |> List.rev |> stringof 
;;
  
let rec generate_rotations b =
  let rec gr reference reverence a =
    match reference with
    | x :: xs ->
       let a =
         ((List.rev reverence) @ (x+1 :: xs))
         :: a
       in
       gr xs (x :: reverence) a
    | [] -> a
  in
  gr (repeat 0 b) [] [] 
;;
  
let mc_cache = ref emptymap ;;
let rec mc n b =
  match n, b with
  | 0, _ when b >= 0 -> [ repeat 0 b ]
  | _, 1 when n >= 0 -> [ [ n ] ]
  | 1, _ when b >= 0 -> generate_rotations b
  | _, _ when n >= 0 && b >= 0 -> 
     let find_or_call n b = 
       let k = (string_of_int n) ^ "~" ^ (string_of_int b) in
       find_or k !mc_cache (fun () -> mc n b)
     in
     let l, r = find_or_call (n-1) b, find_or_call n (b-1) in
     let r = List.map
               (fun s -> 0 :: s) r in
     let l = List.map
               (function
                | [] -> []
                | x :: xs -> (x+1) :: xs) l in
     
     let mcnb = l @ r in
     let k = (string_of_int n) ^ "~" ^ (string_of_int b) in
     let _ = mc_cache := IMap.add k mcnb !mc_cache in
     mcnb

  | _ -> []
;;

let mcnz n b =
  mc (n-b) b |> List.map (List.map ((+) 1))
;;

let pair_wise l1 l2 =
  let rec pw l o a =
    match l with
    | x :: l -> 
       let a = List.fold_left
                   (fun a y -> (x, y) :: a) a o
       in
       pw l o a
       
    | [] -> a
  in
  pw l1 l2 []
;;
  
let c_cache = ref emptymap ;;
let rec c n = 
  match n <= 0 with
  | true -> [ F Place ]
  | false -> 
     let find_or_call n =
       let k = string_of_int n in
       find_or k !c_cache (fun () -> c n)
     in
     let a = ref [] in
     let _ = for i = 0 to n - 1 do
               let l = find_or_call i in
               let r = find_or_call (n-1-i) in
               a := (pair_wise l r |> List.map (fun (x,y) -> A(x,y))) @ !a         
             done
     in
     let k = string_of_int n in
     let _ = c_cache := IMap.add k !a !c_cache in
     !a
;;

let abstract t =
  match t with
  | L ( i, _ ) -> L ( i+1, t )
  | _ -> L ( 0, t )
;;

let replace_leaf stp c =
  let rec rl stp c =
    match c with
    | A ( l, r ) -> let l, stp = rl stp l in
                    let r, stp = rl stp r in
                    A (l, r), stp

    | F Place -> List.hd stp, List.tl stp

    | _ -> c, stp
  in
  rl stp c |> fst
;;

let replace_leafs cs stps =
  let rec rl a stps =
    match stps with
    | stp :: stps ->
       let stp = List.map (replace_leaf stp) cs in
       rl (stp @ a) stps

    | [] -> a
  in
  rl [] stps
;;

let combine_all tups =
  let rec ca tups a =
    match tups with
    | tup :: tups ->
       List.fold_left
         (fun a' t ->
           List.map
             (fun x -> t :: x)
             a
           |> (@) a')
         []
         tup
    |> ca tups
       
    | [] -> List.map
              List.rev
              a
  in
  ca tups [[]]
;;
  
let l_cache = ref emptymap ;;
let rec l n =
  match n <= 0 with
  | true -> [F Place]
  | false ->
     let a = ref (
                   (List.map
                      (abstract)
                      (l (n-1))
                   )
               )
     in
     let _ = for i = 1 to n - 1 do
               let cs = c i in
               let mcs = mc (n-i-1) (i+1) in
               let subtree_permutations = mcs
                                          |> List.map
                                               (fun mc -> mc |> List.map l |> combine_all)
                                          |> List.flatten
               in
               a :=
                 (replace_leafs cs subtree_permutations
                  |> List.map abstract
                  |> function
                    | [] -> cs
                    | x -> x)
                 @ !a
             done
     in
     let k = string_of_int n in
     let _ = l_cache := IMap.add k !a !l_cache in
     !a      
;;

let a_cache = ref emptymap ;;
let a n =
  let a = ref [] in
  let _ = for i = 1 to n-1 do
            let cs = c i in
            let mcnzs = mcnz (n-i) (i+1) in
            let stps = mcnzs
                       |> List.map
                            (fun mc -> mc |> List.map l |> combine_all)
                       |> List.flatten
            in
            a := (replace_leafs cs stps) @ !a
          done
  in
  let k = string_of_int n in
  let _ = a_cache := IMap.add k !a !a_cache in
  !a
;;

let f i = F (X i) ;;
let range_fun base until incr constructor =
  let rec rf i =
    match i >= until with
    | true -> [] 
    | false -> (constructor i) :: rf (i + incr)
  in
  rf base
;;
  
let globally_index tree =
  let rec gi n tree =
    match tree with
    | A ( l, r ) ->
       let l = gi n l in
       let r = gi n r in
       let reform l =
         A ( List.hd l, List.hd (List.tl l))
       in
       combine_all [l;r] |> List.map reform

    | L ( i, tree ) ->
       let tree = gi (n+1) tree in
       List.map (fun t -> L ( i, t )) tree

    | F Place ->
       range_fun 0 n 1 f

    | _ -> [tree]
  in
  gi 0 tree
;;


let locally_index tree =
  let rec li n nu tree =
    match tree with
    | A ( l, r ) ->
       let l = li n true l in
       let r = li n true r in
       let reform l =
         A ( List.hd l, List.hd (List.tl l))
       in
       combine_all [l;r] |> List.map reform

    | L ( i, tree ) when nu ->
       let tree = li 1 false tree in
       List.map (fun t -> L ( i, t)) tree

    | L ( i, tree ) ->
       let tree = li (i+1) false tree in
       List.map (fun t -> L (i, t)) tree

    | F Place ->
       range_fun 0 n 1 f

    | _ -> [tree]

  in
  li 0 false tree
;;

let maybe_replace_leaf stp c =
  let rec mrl stp c =
    match c with
    | A ( F Place, F Place) -> (match stp with
                                   | F Place :: r :: stp ->
                                      Some (A(F Place, r)), stp 
                                      
                                   | l :: F Place :: stp ->
                                      Some (A(l, F Place)), stp
                                      
                                   | _ -> None, stp)
                                 
    | A ( l , r ) -> (let l, stp = mrl stp l in
                     let r, stp = mrl stp r in
                     match l, r with
                     | None, _ | _, None -> None, stp
                     | Some l, Some r -> 
                        Some (A (l, r)), stp)
       
    | F Place -> Some (List.hd stp), List.tl stp

    | _ -> Some c, stp
  in
  mrl stp c |> fst
;;

let rec some_list xs =
  match xs with
  | Some x :: xs -> x :: some_list xs
  | None :: xs -> some_list xs
  | [] -> []
;;

let maybe_replace_leafs cs stps =
  let rec rl a stps =
    match stps with
    | stp :: stps ->
       let stp = List.map (maybe_replace_leaf stp) cs in
       rl (stp @ a) stps

    | [] -> some_list a
  in
  rl [] stps
;;

let n_cache = ref emptymap ;;
let rec normalized n =
  match n <= 0 with
  | true -> [F Place]
  | false ->
     let a = ref (
                   (List.map
                      (abstract)
                      (normalized (n-1))
                   )
               )
     in
     let _ = for i = 1 to n - 1 do
               let cs = c i in
               let mcs = mc (n-i-1) (i+1) in
               let subtree_permutations = mcs
                                          |> List.map
                                               (fun mc -> mc |> List.map l |> combine_all)
                                          |> List.flatten
               in
               a :=
                 (maybe_replace_leafs cs subtree_permutations
                  |> List.map abstract
                  |> function
                    | [] -> cs
                    | x -> x)
                 @ !a
             done
     in
     let k = string_of_int n in
     let _ = l_cache := IMap.add k !a !l_cache in
     !a      
;;

let a006318 n = l n |>  List.map lchr ;;
let q_unappliable n = normalized n |> List.map lchr ;;
  
let a220895 n = l n |> List.map globally_index |> List.flatten |> List.map lchr ;;
let a220894 n = l n @ a n |> List.map globally_index |> List.flatten |> List.map lchr ;;

let q n = normalized n |> List.map globally_index |> List.flatten |> List.map lchr ;;  

  
  ()

           
