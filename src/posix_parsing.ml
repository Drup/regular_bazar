(** Posix parsing.

    Algorithm from:
    *POSIX Lexing with Derivatives of Regular Expressions*
    by Fahad Ausaf, Roy Dyckhoff, and Christian Urban
*)

type label = string

type t =
  | Void
  | Epsilon
  | Char of Char.t
  | Alternative of t * t
  | Sequence of t list
  | Repetition of t
  | Label of label * t

let rec nullable = function
  | Void -> false
  | Epsilon -> true
  | Char _ -> false
  | Alternative (r1, r2) -> nullable r1 || nullable r2
  | Sequence rs -> List.for_all nullable rs
  | Repetition r -> nullable r
  | Label (_,r) -> nullable r

(* Should be smart *)
let seq l =
  let rec accum = function
    | [] -> []
    | Sequence r :: l -> r @ accum l
    | r :: l -> r :: accum l
  in
  match l with
  | [v] -> v
  | l -> Sequence (accum l)
let rep r = Repetition r
let label l r = Label (l, r)
let c x = Char x
let (+++) a b = seq [a;b]
let (|||) a b = Alternative (a,b)

let rec deriv c = function
  | Void -> Void
  | Epsilon -> Void
  | Char c' ->
    if Char.equal c c' then Epsilon else Void
  | Alternative (r1, r2) ->
    deriv c r1 ||| deriv c r2
  | Sequence rs ->
    deriv_seq c rs
  | Repetition r ->
    deriv c r +++ rep r
  | Label (l, r) -> Label (l, deriv c r)

and deriv_seq c = function
  | [] -> Void
  | r::rs ->
    let start = deriv c r +++ seq rs in
    if nullable r then
      start ||| deriv_seq c rs
    else
      start
      
let rec deriv_chars l r = match l with
  | [] -> r
  | c::l -> deriv_chars l (deriv c r)

type value =
  | Unit
  | Char of Char.t
  | Left of value
  | Right of value
  | Sequence of value list
  | List of value list
  | Label of label * String.t

let rec inhabit v r = match v, r with
  | Unit, Epsilon -> true
  | Char c, Char c' when Char.equal c c' -> true
  | Left v, Alternative (r, _)
  | Right v, Alternative (_, r) ->
    inhabit v r
  | Sequence vs, Sequence rs ->
    List.for_all2 inhabit vs rs
  | List vs, Repetition r ->
    List.for_all (fun v -> inhabit v r) vs
  | _, _ -> false

(* Value building *)

exception Not_nullable

let rec mkeps = function
  | Void -> raise Not_nullable
  | Char _ -> raise Not_nullable
  | Epsilon -> Unit
  | Sequence rs -> Sequence (List.map mkeps rs)
  | Alternative (r1, r2) ->
    if nullable r1 then Left (mkeps r1) else Right (mkeps r2)
  | Repetition _ -> List []
  | Label (l, _) -> Label (l, "")

let rec inject c (r : t) (v : value) = match r, v with
  | Char d, Unit ->
    assert (Char.equal c d);
    Char c
  | Alternative (r, _), Left v ->
    Left (inject c r v)
  | Alternative (_, r), Right v ->
    Right (inject c r v)
  | Sequence rs, v ->
    inject_sequence c rs v    
  | Repetition r, Sequence [v; List vs] ->
    List (inject c r v :: vs)
  | Label (l, _r), Label (l', s) ->
    assert (l = l');
    Label (l, CCString.of_char c ^ s)
  | _ -> assert false

and inject_sequence c (rs : t list) (v : value) = match rs, v with
  | [], _ -> assert false
  | [r], Sequence [v] -> inject c r v
  | r :: _,
    ( Sequence (v :: vs) | Left (Sequence (v :: vs))) -> 
    Sequence (inject c r v :: vs)
  | r :: rs, Right v ->
    Sequence [mkeps r; inject_sequence c rs v]
  | _ -> assert false

let lexer r str =
  let rec loop r str = match str () with
    | Seq.Nil ->
      if nullable r then Some (mkeps r) else None
    | Seq.Cons (c, str) ->
      match loop (deriv c r) str with
      | None -> None
      | Some v -> Some (inject c r v)
  in
  loop r @@ CCString.to_seq str
