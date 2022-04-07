module M = struct
  type t = Char.t
  let compare = Char.compare
  let equal = Char.equal
  let pp = Fmt.char
  let hash = Hashtbl.hash
end
include M
module Set = CCSet.Make(M)
module Map = CCMap.Make(M)
module Tbl = CCHashtbl.Make(M)

module Infix = struct
  let ( .@() ) a b = Tbl.find a b
  let ( .@?() ) a b = Tbl.find a b
  let ( .@()<- ) a b c = Tbl.add a b c
end
      

module Eps = struct
  type t = Eps | A of M.t
  let as_opt = function Eps -> None | A c -> Some c
  let compare x1 x2 = CCOption.compare M.compare (as_opt x1) (as_opt x2)
  let pp fmt = function
    | Eps -> Fmt.pf fmt "ε"
    | A a -> M.pp fmt a
end
module EpsSet = CCSet.Make(Eps)
module EpsMap = CCMap.Make(Eps)
