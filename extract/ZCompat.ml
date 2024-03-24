(*Convert between Coq Z and OCaml Z.t (for Zmap data structure)*)

(*Requires a positive Z.t*)
let to_pos (z: Z.t) : BinNums.positive =
  let rec build_pos (n: int) (base: BinNums.positive) : BinNums.positive =
    if n < 0 then base
    else 
      let b = Z.testbit z n in
      if b then build_pos (n-1) (Coq_xI base)
      else build_pos (n-1) (Coq_xO base)
  in build_pos (Z.numbits z - 2) Coq_xH  

let to_Z (z: Z.t) : BinNums.coq_Z =
  if Z.equal z Z.zero then Z0
  else if Z.gt z Z.zero then Zpos (to_pos z)
  else Zneg (to_pos (Z.neg z))

let of_pos (p: BinNums.positive) : Z.t =
  (*TODO: tail recursive?*)
  let rec of_pos_aux (p: BinNums.positive) : Z.t =
    match p with
    | Coq_xH -> Z.one
    | Coq_xO p' -> Z.shift_left (of_pos_aux p') 1 (*2 * z*)
    | Coq_xI p' -> Z.succ (Z.shift_left (of_pos_aux p') 1) (*2 * z + 1*)
  in
  of_pos_aux p

let of_Z (z: BinNums.coq_Z) : Z.t =
  match z with
  | Z0 -> Z.zero
  | Zpos p -> of_pos p
  | Zneg p -> Z.neg (of_pos p)

let to_Z_big = fun x -> to_Z (BigInt.to_Z x)
let of_Z_big = fun x -> BigInt.of_Z (of_Z x)



  (*OCaml function to_pos - gives positive of (x+1) because
  we allow 0 values
  (*Go from [numbits x]-1 down to 0*)
  let to_pos (x: Z.t) = 
    let rec build_pos (n: int) (x: Z.t) (base: positive) : positive =
      if n < 0 then base else
      let b = Z.testbit x n in
      if b then build_pos (n-1) (xI base)
      else build_pos (n-1) (xO base)
    in build_pos (Z.numbits x - 1) (Z.succ x) xH
*)