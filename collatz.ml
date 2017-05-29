(*

  An abstract machine which simulates the collatz problem using reductions over
  binary strings.

  "collatz n" will show the path in decimal
  "printbinpath (collatz n)" will show the path in binary

*)
(*

  0ˣ invalid

  11 × 010T → 011 (11 × T)
  11 × 0ˣ10T → 0ˣ11 (11 × T)
  11 × 01ʸ0T → 0101ʸ⁻²0 (1 + 11 × T)
  11 × 0ˣ1ʸ0T → 0ˣ101ʸ⁻²0 (1 + 11 × T)

  11 × 10ʸ1T → 110ʸ⁻¹1 (1 + 11 × T)
  11 × 1ˣ0ʸ1T → 101ˣ⁻²010ʸ⁻²1 (1 + 11 × T)
  11 × 101T → 111 (1 + 11 × T)
  11 × 1ˣ01T → 101ˣ⁻²00 (01 + 11 × T)


  1 + 11 × 10ʸ1T 
  → 0010ʸ⁻²1 (1 + 11 × T) 
  1 + 11 × 1ˣ0ʸ1T 
  → 01ˣ⁻¹010ʸ⁻²1 (1 + 11 × T) 
  1 + 11 × 101T 
  → 000 (01 + 11 × T) 
  1 + 11 × 1ˣ01T 
  → 01ˣ⁻¹00 (01 + 11 × T) 
  1 + 11 × 010T 
  → 111 (11 × T)
  1 + 11 × 0ˣ10T 
  → 10ˣ⁻¹11 (11 × T)
  1 + 11 × 01ʸ0T 
  → 1101ʸ⁻²0 (1 + 11 × T)
  1 + 11 × 0ˣ1ʸ0T 
  → 10ˣ⁻¹101ʸ⁻²0 (1 + 11 × T)


  01 + 11 × 010T 
  → 000 (1 + 11 × T)
  01 + 11 × 0ˣ10T 
  → 010ˣ⁻²11 (11 × T)
  01 + 11 × 01ʸ0T 
  → 001ʸ⁻¹0 (1 + 11 × T)
  01 + 11 × 0ˣ1ʸ0T 
  → 010ˣ⁻²101ʸ⁻²0 (1 + 11 × T)
  01 + 11 × 10ʸ1T 
  → 1010ʸ⁻²1 (1 + 11 × T)
  01 + 11 × 1ˣ0ʸ1T 
  → 1ˣ010ʸ⁻²1 (1 + 11 × T)
  01 + 11 × 101T 
  → 100 (01 + 11 × T)
  01 + 11 × 1ˣ01T 
  → 1ˣ00 (01 + 11 × T)

*)


type abstr = F of int | T of int 

let classify bl =
  let rec blf i bl = 
    match bl with
      | [] -> [ F i ]
      | false :: bl -> blf (i + 1) bl
      | true :: bl -> F i :: blt 1 bl

  and blt i bl =
    match bl with
      | [] -> [ T i ]
      | false :: bl -> T i :: blf 1 bl
      | true :: bl -> blt (i + 1) bl
  in
  match bl with
    | true :: bl -> blt 1 bl
    | false :: bl -> blf 1 bl


let reduce ab n =
  match ab with
    | F i -> F (i-n)
    | T i -> T (i-n)


let rec f abl = 
  match abl with
    | [] -> []

    | [ x ] -> (
      match x with
	| T 1 -> [ T 2 ]
	| T n -> [ T 1 ; F 1 ; reduce x 2 ; F 1 ; T 1 ]
    )

    | [ x ; y ] -> (
      match x , y with
	| F n , T 1 -> [ F n ; T 2 ]
	| F n , T m -> [ F n ; T 1 ; F 1 ; reduce y 2 ; F 1 ; T 1 ]
    )

    | x :: y :: rest -> 
      match x , y with
	| T 1 , F 1 -> 
	  T 3 :: ( recurse fp rest ) 
	    
	| T 1 , F n -> 
	  T 2 :: ( reduce y 1 ) :: T 1 :: ( recurse fp rest )
	    
	| T n , F 1 -> 
	  T 1 :: F 1 :: ( reduce x 2 ) :: F 2 :: ( recurse fpp rest )
	    
	| T n , F m -> 
	  T 1 :: F 1 :: ( reduce x 2 ) :: F 1 :: T 1 :: ( reduce y 2 ) :: T 1 :: ( recurse fp rest )
	    
	| F n , T 1 ->
	  x :: T 2 :: ( recurse f rest )	

	| F n , T m -> 
	  x :: T 1 :: F 1 :: ( reduce y 2 ) :: F 1 :: ( recurse fp rest )

and fp abl = 
  match abl with
    | [] -> [ T 1 ]

   | [ x ] -> (
      match x with
	| T 1 -> [ F 2 ; T 1 ]
	| T n -> [ F 1 ; reduce x 1 ; F 1 ; T 1 ]
    )

    | [ x ; y ] -> (
      match x , y with
	| F n , T 1 -> 
	  [ T 1 ; reduce x 1 ; T 2 ]
	    
	| F n , T m -> 
	  [ T 1 ; reduce x 1 ; T 1 ; F 1 ; reduce y 2 ; F 1 ; T 1 ]
    )

    | x :: y :: rest -> 
      match x , y with
	| T 1 , F 1 ->
	  F 3 :: ( recurse fpp rest )

	| T 1 , F n ->
	  F 2 :: T 1 :: ( reduce y 2 ) :: T 1 :: ( recurse fp rest )

	| T n , F 1 ->
	  F 1 :: ( reduce x 1 ) :: F 2 :: ( recurse fpp rest )

	| T n , F m ->
	  F 1 :: ( reduce x 1 ) :: F 1 :: T 1 :: ( reduce y 2 ) :: T 1 :: ( recurse fp rest )

	| F n , T 1 ->
	  T 1 :: ( reduce x 1 ) :: T 2 :: ( recurse f rest )

	| F n , T m -> 
	  T 1 :: ( reduce x 1 ) :: T 1 :: F 1 :: ( reduce y 2 ) :: F 1 :: ( recurse fp rest )


and fpp abl = 
  match abl with
    | [] -> [ F 1 ; T 1 ]

    | [ x ] -> ( 
      match x with
	| T 1 -> [ T 1 ; F 1 ; T 1 ]
	| T n -> [ x ; F 1 ; T 1 ]
    )

    | [ x ; y ] -> (
      match x , y with
	| F 1 , T 1 ->
	  [ F 3 ; T 1 ]

	| F n , T 1 ->
	  [ F 1 ; T 1 ; reduce x 2 ; T 2 ]

	| F 1 , T n ->
	  [ F 2 ; reduce y 1 ; F 1 ; T 1 ]

	| F n , T m -> 
	  [ F 1 ; T 1 ; reduce x 2 ; T 1 ; F 1 ; reduce y 2 ; F 1 ; T 1 ]
    )

    | x :: y :: rest ->
      match x , y with
	| T 1 , F 1 ->
	  T 1 :: F 2 :: ( recurse fpp rest )

	| T n , F 1 ->
	  x :: F 2 :: ( recurse fpp rest )

	| T 1 , F n ->
	  T 1 :: F 1 :: T 1 :: ( reduce y 2 ) :: T 1 :: ( recurse fp rest )

	| T n , F m ->
	  x :: F 1 :: T 1 :: ( reduce y 2 ) :: T 1 :: ( recurse fp rest )

	| F 1 , T 1 ->
	  F 3 :: ( recurse fp rest )

	| F 1 , T n ->
	  F 2 :: ( reduce y 1 ) :: F 1 :: ( recurse fp rest )

	| F n , T 1 ->
	  F 1 :: T 1 :: ( reduce x 2 ) :: T 2 :: ( recurse f rest )

	| F n , T m -> 
	  F 1 :: T 1 :: ( reduce x 2 ) :: T 1 :: F 1 :: ( reduce y 2 ) :: F 1 :: ( recurse fp rest )

and recurse whichfunction abl = 
  match abl with
    | F 1 :: rest -> whichfunction rest
    | T 1 :: rest -> whichfunction rest
    | F n :: rest -> whichfunction ( F ( n - 1 ) :: rest )
    | T n :: rest -> whichfunction ( T ( n - 1 ) :: rest )

let div2 abl =
  match abl with
    | F n :: abl -> abl
    | abl -> abl

let rec strip abl =
  match abl with
    | F 0 :: abl -> strip abl
    | T 0 :: abl -> strip abl
    | x :: abl -> x :: strip abl
    | [] -> []

let rec collect abl = 
  match abl with
    | F x :: F y :: rest ->
      collect ( ( F ( x + y ) ) :: rest )

    | T x :: T y :: rest ->
      collect ( ( T ( x + y ) ) :: rest )

    | x :: [] -> x :: []

    | [] -> []

    | x :: rest -> x :: collect rest
  

let blof n = 
  let rec blof n acc =
    if n = 0 then ( List.rev acc )
    else
      if n mod 2 = 0 then
	blof ( n / 2 ) ( false :: acc )
      else
	blof ( n / 2 ) ( true :: acc )
  in
  blof n []

let decof bl =
  let rec decof bl m acc = 
    match bl with
      | false :: bl -> decof bl ( m * 2 ) acc

      | true :: bl -> decof bl ( m * 2 ) ( acc + m )

      | [] -> acc
  in
  decof bl 1 0

let rec repeat i n =
  if n = 0 then
    []
  else
    i :: ( repeat i ( n - 1 ) )

let rec blofabl abl =
  match abl with
    | F n :: abl -> ( repeat false n ) @ ( blofabl abl )
    | T n :: abl -> ( repeat true n ) @ ( blofabl abl )
    | [] -> []

let cat lx xtostr sep = 
  let rec cat lx = 
    match lx with
    | [] -> ""
    | x :: [] -> (xtostr x) ^ ""
    | x :: lx -> (xtostr x) ^ sep ^ (cat lx)
  in
  cat lx

let collatz n = 
  let rec collatz acc abl =
    let abl = fp abl in
    if abl = [ F 2 ; T 1 ] then
      List.rev acc , abl
    else
      let abl = div2 ( collect ( strip abl ) ) in
      collatz ( ( decof ( blofabl abl ) ) :: acc) abl
  in
  let bl = blof n in
  let abl = div2 ( classify bl ) in
  let path , abl = collatz [n] abl in
  let bl = blofabl abl in
  let m = decof bl in
  path

let printdecpath path =
  print_string ( cat path (string_of_int) " -> " );
  print_string "\n"

let string_of_bool b =
  match b with
    | false -> "0"
    | true -> "1"

let binstring_of_int n =
  cat (blof n) (string_of_bool) ""

let printbinpath path = 
  print_string ( cat path (binstring_of_int) " ->\n" );
  print_string "\n"

let test lo hi =
  let rec test i =
    if i = hi then
      ()
    else 
      let _ = collatz i in
      test ( i + 1 )	
  in
  test lo
