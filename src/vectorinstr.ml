(** Past-temporal-Logic to Vector Addition Machine *)

module Name = struct
  type t = int
  let gen =
    let r = ref 0 in
    fun () -> CCRef.get_then_incr r
        
  let rec base26 i =
    Char.chr (i mod 26 + Char.code 'a') ::
    if i > 26 then base26 (i/26) else []
  let pp fmt (x : t) =
    Format.pp_print_string fmt @@ CCString.of_list @@ base26 x
  module Tbl = CCHashtbl.Make(CCString)
end

module Char = Stdlib.Char
module Word = Stdlib.String
  
module PTL = struct
  type t =
    | Atom of Char.t
    | Or of t * t
    | And of t * t
    | Not of t
    | Yesterday of t
    | Since of t * t

  let (||) a b = Or(a,b)
  let (&&) a b = And(a,b)
  let not p = Not p
  let (=>) p1 p2 = Since(p2,p1)
  let yesterday p = Yesterday(p)
  let atom p = Atom(p)

  let rec pp fmt = function
    | Atom c -> Fmt.char fmt c
    | Or (f1, f2) -> Fmt.pf fmt "(%a) ∨ (%a)" pp f1 pp f2
    | And (f1, f2) -> Fmt.pf fmt "(%a) ∧ (%a)" pp f1 pp f2
    | Not f -> Fmt.pf fmt "¬(%a)" pp f
    | Yesterday f -> Fmt.pf fmt "Y(%a)" pp f
    | Since (f1, f2) -> Fmt.pf fmt "(%a) S (%a)" pp f1 pp f2
end

module VectorProg = struct

  type unop =
    | Shift_left
    | Logical_not
    | Mask of Char.t
  let pp_unop fmt = function
    | Shift_left -> Fmt.pf fmt "shift" | Logical_not -> Fmt.pf fmt "lnot"
    | Mask c -> Fmt.pf fmt "mask('%c')" c 

  type binop = 
    | Addition
    | Logical_or
    | Logical_and
    | Logical_xor
  let pp_binop = Fmt.of_to_string @@ function
    | Addition -> "add" | Logical_and -> "land" | Logical_or -> "lor" | Logical_xor -> "xor"

  type t =
    | Input
    | UnOp of unop * t
    | BinOp of binop * t * t

  let unop f p = UnOp(f, p)
  let binop f p1 p2 = BinOp(f, p1, p2)

  let (+) = binop Addition
  let (land) = binop Logical_and
  let (lor) = binop Logical_or
  let (lxor) = binop Logical_xor
  let lnot = unop Logical_not
  let lshift = unop Shift_left

  let carry p1 p2 = (p1 lxor p2) lxor (p1 + p2)

  module M = struct
    type nonrec t = t 
    let equal = (=)
    let hash = Hashtbl.hash
  end
  module Tbl = Hashtbl.Make(M)
  module Hashcons = struct
    type 'a t = 'a Tbl.t
    let make () = Tbl.create 17
    let get = Tbl.find_opt
    let add tbl x n = Tbl.add tbl x n
  end

  type instr =
    | UnOp of Name.t * unop * var
    | BinOp of Name.t * binop * var * var
  and var = Name of Name.t | Input
  type program = instr list * var
  
  let linearize e : program =
    let instrs : instr list ref = ref [] in
    let rec aux hcons (e : t) =
      match Hashcons.get hcons e with
      | Some var -> var
      | None ->
        let var = match e with
          | Input -> Input
          | UnOp (op, e) ->
            let n = Name.gen () in
            let i = UnOp (n, op, aux hcons e) in
            instrs := i :: !instrs ;
            Name n            
          | BinOp (op, e1, e2) ->
            let n = Name.gen () in
            let i = BinOp (n, op, aux hcons e1, aux hcons e2) in
            instrs := i :: !instrs ;
            Name n            
        in
        Hashcons.add hcons e var;
        var
    in
    let return = aux (Hashcons.make ()) e in
    (List.rev !instrs, return)

  let pp_program fmt (l, r) =
    let pp_var fmt = function
      | Input -> Fmt.pf fmt "INPUT" | Name n -> Name.pp fmt n in
    let pp_instr fmt = function
      | UnOp (n, op, var) ->
        Fmt.pf fmt "%a = %a(%a)" Name.pp n pp_unop op pp_var var
      | BinOp (n, op, var1, var2) -> 
        Fmt.pf fmt "%a = %a(%a, %a)" Name.pp n pp_binop op pp_var var1 pp_var var2
    in
    Fmt.pf fmt "@[<v>%a@]@.return %a" (Fmt.list pp_instr) l pp_var r
end

let compile e = 
  let rec aux (p : PTL.t) input : VectorProg.t = match p with
    | PTL.Atom c -> VectorProg.unop (Mask c) input
    | PTL.Or (p1, p2) -> BinOp (Logical_or, aux p1 input, aux p2 input)
    | PTL.And (p1, p2) -> BinOp (Logical_and, aux p1 input, aux p2 input)
    | PTL.Not p -> VectorProg.lnot @@ aux p input
    | PTL.Yesterday p -> UnOp (Shift_left, aux p input)
    | PTL.Since (p1, p2) ->
      let vp1 = aux p1 input and vp2 = aux p2 input in
      let vp_1and2 = VectorProg.(lshift vp2 land vp1) in
      VectorProg.(vp2 lor vp_1and2 lor (vp1 land carry vp1 vp_1and2))
  in
  VectorProg.linearize @@ aux e Input

(* let e = PTL.(atom 'a' => (atom 'b' || atom 'a'))
 * 
 * let p = compile e
 * 
 * let () =
 *   Fmt.pr "@[<v2>Input:@ @[%a@]@]@.@.Output:@.%a@."
 *     PTL.pp e
 *     VectorProg.pp_program p *)
