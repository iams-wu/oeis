open Printf;;
(*

Used to generate the sequence https://oeis.org/A263856

"lexiograph" is the main generator

*)


let bvlt l r =
  let rec aux l r = 
    match l with 
    | [] -> r <> []
    | x :: xs -> 
       match r with
       | [] -> false
       | y :: ys -> 
	  if x = y then
	    aux xs ys
	  else
	    y
  in
  aux l r

let int_sqrt n = 
  (int_of_float (sqrt (float_of_int n)))

let calc_prime_sequence n = 
  let sieve = Array.make n false in
  let b = (int_sqrt n) in
  let rec l i j =
    if j >= n then
      let rec l2 i =
	if i > b then
	  sieve
	else if sieve.(i) then
	  l2 (i+1)
	else
	  l i (i*i)
      in
      l2 (i+1)
    else (
      sieve.(j) <- true;
      l i (j + i)		     
    )
  in
  l 2 4
;;

let rec bvsuc x = 
  match x with
  | [] -> [true]
  | false :: xs -> true :: xs
  | true :: xs -> false :: (bvsuc xs)
;;

let lexinsert lexio item =
  let rec lexinsert lexio item i =
    match lexio with
    | [] -> [item] , i
    | x :: xs -> 
       if bvlt item x then
	 item :: x :: xs , i
       else
	 let xs , i = lexinsert xs item (i+1) in
	 x :: xs , i
  in
  lexinsert lexio item 1
;;

let rec bvstring x =
  match x with
  | false :: xs -> "0" ^ bvstring xs
  | true :: xs -> "1" ^ bvstring xs
  | [] -> ""
;;

let lexiograph n = 
  let sieve = calc_prime_sequence n in
  let rec l1 lexio indices cur i p = 
    if i >= n then
      lexio , List.rev indices
    else if (not sieve.(i)) then (
      let xs , ind = lexinsert lexio cur in 
      l1 xs (ind :: indices) (bvsuc cur) (i+1) (p+1)
    )
    else
      l1 lexio indices (bvsuc cur) (i+1) p
  in
  l1 [] [] [false;true] 2 1
  
let printlexios n =
  let oc = open_out "primes.b" in
  let _ , indices = lexiograph n in
  let rec l1 xs i =
    match xs with
    | x :: xs -> 
       fprintf oc "%d %d\n" i x;
       l1 xs (i+1)
    | [] -> close_out oc
  in
  l1 indices 1

let freqs n =
  let _ , indices = lexiograph n in
  let n = Array.make (n+1) 0 in
  List.iter (fun i -> n.(i) <- n.(i) + 1) indices;
  indices


(* Calculates the average insertion position.

It ends up coming to be .5 (as expected?) *)      
let avg n =
  let _ , indices = lexiograph n in
  let rec l1 i xs tot n =
    match xs with
    | x :: xs -> l1 (i+1) xs (tot+x) (n+i)
    | [] -> (float_of_int tot) /. (float_of_int n)
  in
  l1 1 indices 0 0
