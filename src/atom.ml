module M = struct
  type t = Char.t
  let compare = Char.compare
  let pp = Fmt.char
end
include M
module Set = CCSet.Make(M)
module Map = CCMap.Make(M)

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
