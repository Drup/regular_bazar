(** Regular expressions *)

module rec Internal : sig 
  type t =
    | Epsilon
    | Atom of Atom.t
    | Concat of t list
    | Alt of Set.t
    | Inter of Set.t
    | Rep of int * int option * t
    | Shuffle of t * t
  include CCSet.OrderedType with type t := t
end = struct
  type t =
    | Epsilon
    | Atom of Atom.t
    | Concat of t list
    | Alt of Set.t
    | Inter of Set.t
    | Rep of int * int option * t
    | Shuffle of t * t
  [@@deriving ord] 
end
and Set : CCSet.S with type elt = Internal.t = CCSet.Make (Internal)

include Internal
module Map = Map.Make(Internal)

let equal x y = compare x y = 0

(** Printers *)

let rec pp fmt x = match x with
  | Epsilon -> Fmt.pf fmt "ε"
  | Atom a -> Atom.pp fmt a
  | Concat l -> Fmt.list ~sep:Fmt.nop pp_with_paren fmt l
  | Alt res -> pp_set ~sep:(Fmt.any "|@,") fmt res
  | Inter res -> pp_set ~sep:(Fmt.any "&@,") fmt res
  | Rep (0, None, re) -> Fmt.pf fmt "%a*" pp_with_paren re
  | Rep (1, None, re) -> Fmt.pf fmt "%a+" pp_with_paren re
  | Rep (low, None, re) -> Fmt.pf fmt "%a{%i,}" pp_with_paren re low
  | Rep (low, Some high, re) -> Fmt.pf fmt "%a{%i,%i}" pp_with_paren re low high
  | Shuffle (re, re') -> Fmt.pf fmt "%a%%@,%a" pp_with_paren re pp_with_paren re'

and pp_with_paren fmt x = match x with
  | Epsilon | Atom _ | Rep _ -> pp fmt x
  | _ -> Fmt.parens pp fmt x

and pp_set ~sep fmt res =
  Fmt.iter ~sep Set.iter pp_with_paren fmt res

let to_string = Fmt.to_to_string pp

(** Combinators *)

let epsilon = Epsilon
let void = Alt Set.empty
let atom s = Atom s
let string s = Concat (List.map atom @@ CCString.to_list s)
let char c = atom c
let charset cs = Alt (Set.of_list @@ List.map char cs)
let enumerate c1 c2 =
  if c1 > c2 then Fmt.invalid_arg "Wrong enumeration:%c %c" c1 c2
  else
    let rec aux i m =
      if i > m then []
      else Char.chr i :: aux (i+1) m
    in
    aux (Char.code c1) (Char.code c2)

let any =
  charset @@ enumerate (Char.chr 0) (Char.chr 255)

let concat l =
  let rec aux = function
    | [] -> []
    | Concat l :: l' -> aux (l @ l')
    | Epsilon :: l -> aux l
    (* | Atom s :: Atom s' :: l ->
     *   aux (atom (s ^ s') :: l) *)
    | Alt l :: _ when Set.is_empty l -> [void]
    | x :: l -> x :: aux l
  in
  match aux l with
  | [] -> Epsilon
  | [x] -> x
  | l -> Concat l

let alt l =
  let rec aux acc = function
    | [] -> acc
    | Alt l :: rest -> aux (Set.union l acc) rest
    | x :: l -> aux (Set.add x acc) l
  in
  let s = aux Set.empty l in 
  if Set.cardinal s = 1 then
    Set.choose s
  else
    Alt s

let inter l =
  let rec aux acc = function
    | [] -> acc
    | Alt l :: _ when Set.is_empty l -> Set.empty
    | x :: l -> aux (Set.add x acc) l
  in
  let s = aux Set.empty l in
  let size = Set.cardinal s in
  if size = 0 then
    void
  else if size = 1 then
    Set.choose s
  else
    Inter s

let shuffle e1 e2 = Shuffle (e1, e2)

let rec rep i j x = match i, j, x with
  | 0, Some 0, _ -> Epsilon
  | 1, Some 1, x -> x
  | _, _, Epsilon -> epsilon
  | _, _, Alt l when Set.is_empty l -> epsilon
  | _, _, Rep (i', None, x)
  | _, None, Rep (i', Some _, x) -> rep (i * i') None x
  | _, Some j, Rep (i', Some j', x) -> rep (i * i') (Some (j * j')) x
  | i, j, x -> Rep (i, j, x)

let star x = rep 0 None x
let plus x = rep 1 None x
let opt x = rep 0 (Some 1) x

module Infix = struct
  let ( ||| ) x y = alt [ x ; y ]
  let ( &&& ) x y = inter [ x ;  y ]
  let ( -.- ) x y = concat [ x ; y ]
  let ( %%% ) x y = shuffle x y
end
