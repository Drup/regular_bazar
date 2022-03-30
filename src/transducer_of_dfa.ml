open Dfa

type transducer = state array
and state = action array
and action = {
  next : int ;
  emit : Bitv.t option;
}

(* Sequence of gray code of size n
   Should be upstreamed to bitv eventually
*)
let gray l =
  let first_set v n =
    let rec lookup i =
      if i = n then raise Not_found ;
      if Bitv.unsafe_get v i then i else lookup (i + 1)
    in
    lookup 0
  in
  let gray n =
    let bv = Bitv.create n false in
    let rec iter () =
      Seq.Cons (
        Bitv.copy bv,
        fun () ->
          Bitv.unsafe_set bv 0 (not (Bitv.unsafe_get bv 0));
          Seq.Cons (Bitv.copy bv, fun () ->
              let pos = succ (first_set bv n) in
              if pos < n then begin
                Bitv.unsafe_set bv pos (not (Bitv.unsafe_get bv pos));
                iter ()
              end
              else
                Nil
            ))
    in
    if n > 0 then iter else OSeq.empty
  in
  gray l

let bitcodes nb =
  let l = int_of_float @@ ceil (log (float nb) /. log 2.) in
  gray l

let to_compress { states; initial; transitions; _ } : transducer =
  let init_id = State.id initial in
  let nb_state = StateSet.cardinal states in
  let to_id s = (State.id s - init_id + nb_state) mod nb_state in
  let td = Array.make nb_state [||] in
  let handle_state st0 =
    let id0 = to_id st0 in
    let a0 = Array.make 256 { next = 0 ; emit = None } in
    begin
      match StateMap.get st0 transitions with
      | None -> ()
      | Some trans when Atom.Map.is_empty trans -> ()
      | Some trans when Atom.Map.cardinal trans = 1 ->
        let c, st = Atom.Map.choose trans in
        let id = to_id st in
        let charcode = Char.code c in
        a0.(charcode) <- { next = id ; emit = None }
      | Some trans -> 
        let n = Atom.Map.cardinal trans in
        let bitcs = bitcodes n in
        let trans_seq = Atom.Map.to_seq trans in
        OSeq.iter2 (fun bitc (c, st) ->
            let id = to_id st in
            let charcode = Char.code c in
            a0.(charcode) <- { next = id ; emit = Some bitc }
          ) bitcs trans_seq
    end;
    td.(id0) <- a0
  in
  StateSet.iter (fun st -> handle_state st) states;
  td

let pp ppf (a : transducer) =
  let pp_trans ppf code { next; emit } =
    if next = 0 && emit = None then ()
    else
    Fmt.pf ppf "%c → %i%a@," (Char.chr code) next
      Fmt.(option (fun fmt -> pf fmt " / %a" Bitv.L.print)) emit
  in
  let pp_transtbl ppf i transtbl =
    Fmt.pf ppf "@[<v2>%i:@ " i;
    Array.iteri (pp_trans ppf) transtbl;
    Fmt.pf ppf "@]@,"
  in 
  let pp fmt a =
    Array.iteri (fun i x -> pp_transtbl fmt i x) a
  in
  Fmt.pf ppf "@[<v>%a@]" pp a
[@@ocaml.toplevel_printer]

let compress (td : transducer) =
  let buf = ref (Bitv.create 0 false) in
  let st = ref 0 in
  let add_buf bitc =
    buf := Bitv.append !buf bitc
  in
  let on_char c =
    let code = Char.code c in
    let { next ; emit } = td.(!st).(code) in
    begin match emit with
      | None -> ()
      | Some bitc -> add_buf bitc
    end;
    st := next;
  in
  (fun s -> Iter.iter on_char s; !buf)


let uri_safe_alphabet =
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"

let encode alphabet bitc =
  let (%) b k = if b then 0 else Int.shift_left 1 k in
  let buf = Buffer.create 4 in
  let rec aux = function
    | c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: rest ->
      let i = c1%5 + c2%4 + c3%3 + c4%2 + c5%1 + c6%0 in
      Buffer.add_char buf alphabet.[i];
      aux rest
    | [] -> ()
    | l ->
      Buffer.add_char buf '=';
      List.iter (fun b -> Buffer.add_char buf (if b then '1' else '0')) l
  in
  aux @@ Bitv.fold_right List.cons bitc [];
  Buffer.contents buf


let test re s =
  let re = Parser.parse re in
  let a = Brzozowski_deriv.make re in
  Fmt.epr "Automaton:@.%a" Dfa.pp a;
  let td = to_compress a in
  Fmt.epr "Transducer:@.%a@." pp td;
  let b = compress td @@ CCString.to_iter s in
  Fmt.pr "Result:@.%a@." Bitv.L.print b;
  Fmt.pr "Encoded:@.%s@." (encode uri_safe_alphabet b);
  a, td, b, encode uri_safe_alphabet b
