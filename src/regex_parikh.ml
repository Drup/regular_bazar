(** Parikh image of a regular expression
   
    Implementation of 
    Semi-linear Parikh Images of Regular Expressions via Reduction
    by Bahareh Badban and Mohammad Torabi Dashti
*)

type name = int
let gen = let r = ref 0 in fun () -> incr r; !r

type 'a num = Var of 'a | Nat of int
type 'a eq = 'a * 'a num list 
type 'a atom =
  | Eq of 'a eq
  | Impl of 'a * 'a
type 'a system = 'a atom list

type 'a regex =
  | Atom of 'a
  | Alt of 'a regex list
  | Seq of 'a regex list
  | Star of name * 'a regex

let rec reduce (re0, f) =
  match re0 with
  | Star (_, Atom _) | Atom _ -> [re0, f]
  | Star (n, Seq l) ->
    let re' = Seq (List.map (fun r -> Star (n, r)) l) in
    reduce (re', f)
  | Star (n, Alt l) ->
    let vars = List.map (fun _ -> gen ()) l in
    let re' = Seq (List.map2 (fun n r -> Star (n,r)) vars l) in
    let f' = Eq (n, List.map (fun n -> Var n) vars) :: f in
    reduce (re', f')
  | Star (n, Star (_, re)) ->
    let n' = gen () in
    let re' = Star (n', re) in
    let f' = Impl (n, n') :: f in
    reduce (re', f')
  | Alt l ->
    List.concat_map (fun r -> reduce (r, f)) l
  | Seq l ->
    let ls = CCList.map_product_l (fun r -> reduce (r, f)) l in
    List.map (fun l -> let rs, fs = List.split l in Seq rs, List.concat fs) ls

let get_formulas p (re0, f0) =
  let rec from_re = function
    | Atom v ->
      begin match p v with
        | None -> []
        | Some v' -> [Eq (v', [Nat 1])]
      end
    | Seq l ->
      List.concat_map from_re l
    | Star (n, Atom v) ->
      begin match p v with
        | None -> []
        | Some v' -> [Eq (n, [Var v'])]
      end
    | _ -> assert false
  in
  from_re re0 @ f0

let gather_impls f0 =
  let h = Hashtbl.create 7 in
  let rec gather f eqs = match f with
    | [] -> eqs
    | Eq eq :: rest -> gather rest (eq::eqs)
    | Impl (n, n') :: rest -> 
      CCHashtbl.add_list h n n';
      gather rest eqs
  in
  let eqs = gather f0 [] in
  eqs, h

let remove_impl f0 =
  let eqs0, h = gather_impls f0 in
  let rec split_cases (eqs : int eq list) = function
    | [] -> [CCList.uniq ~eq:(=) @@ eqs]
    | (n, ns) :: rest ->
      let l1 =
        split_cases (List.map (fun n' -> (n', [Nat 0])) (n::ns) @ eqs) rest in
      let l2 =
        let nv = gen () in
        split_cases ((n, [Var nv; Nat 1]) :: eqs) rest
      in
      l1 @ l2
  in
  split_cases eqs0 @@ CCHashtbl.to_list h

let re2cnf p re =
  let l = reduce (re, []) in
  let l' = List.map (get_formulas p) l in
  List.concat_map remove_impl l'

(* let p0 v = Some v
 * 
 * let star r = Star (gen(),r)
 * let (++) r r' = Seq [r;r']
 * let (||) r r' = Alt [r; r']
 * 
 * let re0 = star @@ (Atom (gen()) ++ Atom (gen()) || Atom(gen()) ) || Atom(gen())
 * 
 * let f = re2cnf p0 re0 *)
