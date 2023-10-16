open Parse_dump

(** Check if bitpattern pairs [bitpatterns] match opcode of [line].
    On success, calls [f] to generate the SMT constraints
    and returns a new line with the constraints added. *)
let add_constraint_checked bitpatterns f line =
  (* Convert string opcode to Int32. *)
  let opcode = Int32.of_string ("0x" ^ line.dl_opcode) in
  (* Check if all ones are ones and all zeros are zeros in opcode.*)
  let match_bitpattern (ones, zereos) =
    (* Check if all expected ones are one. *)
    (* All expected ones should be marked with a one. *)
    Int32.logand opcode ones = ones &&
    (* Check if all expected zeroes are zero. *)
    (* All expected zeros should also be marked with a one. *)
    Int32.logand opcode zereos = 0l
  in
  (* Check if at least one bitpattern pair matches *)
  match List.exists match_bitpattern bitpatterns with
  | false -> None
  | true ->
    (* Decode opcode and generate SMT constraints. *)
    let smts = f opcode in
    (* Create ASM constraint from SMT constraint. *)
    let mk_constraint smt =
      (* Use negative number to indicate that the constraint does not exist in any file. *)
      let line_number = -123 in
      (* Be distinct from user-added constraints that start with //@constraint: *)
      let original_line = "no original line - auto-generated" in
      (* Create constraint data. *)
      (line_number, original_line, smt)
    in
    (* Create ASM constraint from every SMT constraint. *)
    let cs = List.map mk_constraint smts in
    (* Add constraints to existing ones. *)
    List.iter (Printf.printf "Generated for %s: %s\n" line.dl_line_orig) smts;
    Some {line with dl_constrs = cs @ line.dl_constrs}

(** Convert register [reg] to SMT register name.
   Maps the stack pointer register to [SP_EL2]. *)
let reg_SMT reg = if reg == 31 then "SP_EL2" else Printf.sprintf "R%u" reg

(** Extract bits [f] to [t] from [opcode]. *)
let bits_from_to f t opcode =
  let x = Int32.shift_left opcode (31 - t) in
  let y = Int32.shift_right_logical x (31 - t + f) in
  Int32.to_int y

(* Add constraints for a specific [STR] and [LDR] variant. *)
let ldr_str_constraints = add_constraint_checked
  [
    (* STR (immediate; unsigned offset)*)
    (0b10_111_0_01_00_000000000000_00000_00000l
    ,0b00_000_1_10_11_000000000000_00000_00000l);
    (* LDR (immediate; unsigned offset) *)
    (0b10_111_0_01_01_000000000000_00000_00000l
    ,0b00_000_1_10_10_000000000000_00000_00000l);
  ] @@ fun opcode ->
    (* Decode. Variable names are the same as in the ARM manual. *)
    let rn = bits_from_to 5 9 opcode in
    let imm12 = bits_from_to 10 21 opcode in
    let pimm12 = imm12 * 8 in
    let xn_or_sp = reg_SMT rn in
    (* Generate SMT constraints (physical address space limit and alignment). *)
    [Printf.sprintf "= (bvand (bvadd %s 0x%016x) 0xfff0000000000007) 0x0000000000000000" xn_or_sp pimm12]

let ldrb_strb_constraints = add_constraint_checked
  [
    (* STRB (register; shifted register variant) *)
    (0b00_111_0_00_00_1_00000_011_0_10_00000_00000l
    ,0b11_000_1_11_11_0_00000_100_0_01_00000_00000l);
    (* LDRB (register; shifted register variant) *)
    (0b00_111_0_00_01_1_00000_000_0_10_00000_00000l
    ,0b11_000_1_11_10_0_00000_000_0_01_00000_00000l);
  ] @@ fun opcode ->
    let rn = bits_from_to 5 9 opcode in
    let xn_or_sp = reg_SMT rn in
    let rm = bits_from_to 16 20 opcode in
    let xm = reg_SMT rm in
    [Printf.sprintf "= (bvand (bvadd %s %s) 0xfff0000000000000) 0x0000000000000000" xn_or_sp xm]
 

let ldp_stp_constraints = add_constraint_checked
  [
    (* STP (64-bit variant; signed offset) *)
    (0b00_101_0_010_0_0000000_00000_00000_00000l
    ,0b01_010_1_101_1_0000000_00000_00000_00000l);
    (* LDP (64-bit variant; signed offset) *)
    (0b00_101_0_010_1_0000000_00000_00000_00000l
    ,0b01_010_1_101_0_0000000_00000_00000_00000l);
  ] @@ fun opcode ->
    let rt = bits_from_to 0 4 opcode in
    let rn = bits_from_to 5 9 opcode in
    let rt2 = bits_from_to 10 14 opcode in
    let imm7 = bits_from_to 15 21 opcode in
    let xt1 = rt in
    let xt2 = rt2 in
    let xn_or_sp = reg_SMT rn in
    let offset = imm7 * 8 in
    let offset_xt1 = offset in
    let offset_xt2 = offset + 8 in
    let smt1 = Printf.sprintf "= (bvand (bvadd %s 0x%016x) 0xfff0000000000007) 0x0000000000000000" xn_or_sp offset_xt1 in
    let smt2 = Printf.sprintf "= (bvand (bvadd %s 0x%016x) 0xfff0000000000007) 0x0000000000000000" xn_or_sp offset_xt2 in
    [smt1; smt2]


let constraints = [ldr_str_constraints; ldrb_strb_constraints; ldp_stp_constraints]

let dosth (lines : decomp_line list) =
  (* Given a line, return the first constraint that is not None in the list of constraints *)
  let find_constraint line = List.find_map (fun c -> c line) constraints in
  (* Add the first applicable constraint(s) to the line, or return the line again if none applicable *)
  let add_constraints line = Option.value ~default:line (find_constraint line) in
  (* Try to add constraints for every line *)
  List.map add_constraints lines
