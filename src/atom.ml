type t = Char.t
let compare = Char.compare
module Map = CCMap.Make(Char)
let pp = Fmt.char
