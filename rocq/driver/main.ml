(* The untrusted driver.

   Everything verified is in rocq_horn_core.ml and rocq_owlrl_core.ml, which are
   extracted from the theories and read by nobody. This file opens paths, hands
   their bytes to a checker, prints one JSON object and returns an exit code. It
   decides nothing about what a certificate says: no splitting, no trimming, no
   normalising, no fallback.

     oo-horn-rocq check RULES.tsv ASSERTED.tsv HORN.tsv   oo-horn (Horn)
     oo-horn-rocq cert  ASSERTED.tsv CERT.tsv             oo-cert (OWL-RL)

   0 accepted, 1 rejected, 2 unreadable or unparseable, 70 the checker itself
   failed. The fourth code is not decoration: OCaml exits an uncaught exception
   with status 2, which is this tool's code for a parse error, so a Stack_overflow
   inside the extracted checker came out looking like a refusal to read the file.
   70 is EX_SOFTWARE from sysexits, and nothing else in this tool uses it. *)

let rec nat_to_int (n : Rocq_horn_core.nat) : int =
  match n with Rocq_horn_core.O -> 0 | Rocq_horn_core.S m -> 1 + nat_to_int m

let bool_of_rocq (b : Rocq_horn_core.bool) : bool =
  match b with Rocq_horn_core.True -> true | Rocq_horn_core.False -> false

(* Rocq's Ascii constructor is little endian: the first argument is bit 0. *)
let ascii_of_char (c : char) : Rocq_horn_core.ascii =
  let n = Char.code c in
  let b i = if n land (1 lsl i) <> 0 then Rocq_horn_core.True else Rocq_horn_core.False in
  Rocq_horn_core.Ascii (b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7)

let rocq_string (s : string) : Rocq_horn_core.string =
  let acc = ref Rocq_horn_core.EmptyString in
  for i = String.length s - 1 downto 0 do
    acc := Rocq_horn_core.String (ascii_of_char s.[i], !acc)
  done;
  !acc

let rec nat_to_int_o (n : Rocq_owlrl_core.nat) : int =
  match n with Rocq_owlrl_core.O -> 0 | Rocq_owlrl_core.S m -> 1 + nat_to_int_o m

let ascii_of_char_o (c : char) : Rocq_owlrl_core.ascii =
  let n = Char.code c in
  let b i = if n land (1 lsl i) <> 0 then Rocq_owlrl_core.True else Rocq_owlrl_core.False in
  Rocq_owlrl_core.Ascii (b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7)

let rocq_string_o (s : string) : Rocq_owlrl_core.string =
  let acc = ref Rocq_owlrl_core.EmptyString in
  for i = String.length s - 1 downto 0 do
    acc := Rocq_owlrl_core.String (ascii_of_char_o s.[i], !acc)
  done;
  !acc

let read_file (path : string) : string =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let which_file = function
  | 0 -> "rules"
  | 1 -> "asserted"
  | _ -> "certificate"

let usage () =
  prerr_endline "usage: oo-horn-rocq check RULES.tsv ASSERTED.tsv HORN.tsv";
  prerr_endline "       oo-horn-rocq cert  ASSERTED.tsv CERT.tsv";
  exit 2

let read_two a b =
  try Some (read_file a, read_file b)
  with Sys_error m -> prerr_endline ("cannot read: " ^ m); None

let read_three a b c =
  try Some (read_file a, read_file b, read_file c)
  with Sys_error m -> prerr_endline ("cannot read: " ^ m); None

(* oo-horn: the Horn rule set, theorem entails_of_builtin_horn. *)
let run_horn rpath gpath dpath =
  match read_three rpath gpath dpath with
  | None -> exit 2
  | Some (rtxt, gtxt, dtxt) -> (
      let result =
        try Ok (Rocq_horn_core.run (rocq_string rtxt) (rocq_string gtxt) (rocq_string dtxt))
        with e -> Error (Printexc.to_string e)
      in
      match result with
      | Error msg ->
          prerr_endline
            ("the checker failed rather than answering: " ^ msg
             ^ " (exit 70; this is NOT a verdict and NOT a parse error)");
          exit 70
      | Ok outcome -> (
          match outcome with
          | Rocq_horn_core.Accepted (b, nr, ng, ns) ->
              let builtin = bool_of_rocq b in
              let verdict =
                if builtin then "entailed" else "entailed_under_supplied_rules"
              in
              let thm =
                if builtin then "OOCertRocq.entails_of_builtin_horn"
                else "OOCertRocq.horn_certificate_sound"
              in
              let means =
                if builtin then
                  "every conclusion is true in every model of the asserted graph"
                else
                  "every conclusion is true in every model of the asserted graph THAT \
                   ALSO SATISFIES the supplied rules; the rules themselves are assumed, \
                   not checked"
              in
              Printf.printf
                "{\"ok\":true,\"kernel\":\"rocq\",\"verdict\":\"%s\",\"rules\":%d,\"asserted\":%d,\"derivations\":%d,\"theorem\":\"%s\",\"means\":\"%s\"}\n"
                verdict (nat_to_int nr) (nat_to_int ng) (nat_to_int ns) thm means;
              exit 0
          | Rocq_horn_core.Rejected (nr, ng, ns) ->
              Printf.printf
                "{\"ok\":false,\"kernel\":\"rocq\",\"rules\":%d,\"asserted\":%d,\"derivations\":%d}\n"
                (nat_to_int nr) (nat_to_int ng) (nat_to_int ns);
              exit 1
          | Rocq_horn_core.ParseError w ->
              prerr_endline ("parse error in the " ^ which_file (nat_to_int w) ^ " file");
              exit 2))

(* oo-cert: the full OWL-RL rule set, theorem check_ccert_sound. *)
let run_cert gpath dpath =
  match read_two gpath dpath with
  | None -> exit 2
  | Some (gtxt, dtxt) -> (
      let result =
        try Ok (Rocq_owlrl_core.run_owlrl (rocq_string_o gtxt) (rocq_string_o dtxt))
        with e -> Error (Printexc.to_string e)
      in
      match result with
      | Error msg ->
          prerr_endline
            ("the checker failed rather than answering: " ^ msg
             ^ " (exit 70; this is NOT a verdict and NOT a parse error)");
          exit 70
      | Ok outcome -> (
          match outcome with
          | Rocq_owlrl_core.Accepted (_b, _nr, ng, ns) ->
              Printf.printf
                "{\"ok\":true,\"kernel\":\"rocq\",\"verdict\":\"entailed\",\"asserted\":%d,\"derivations\":%d,\"theorem\":\"OOCertRocq.check_ccert_sound\",\"means\":\"every conclusion is true in every OWL-RL model of the asserted graph, over the full rule set including the four RDF-list rules\"}\n"
                (nat_to_int_o ng) (nat_to_int_o ns);
              exit 0
          | Rocq_owlrl_core.Rejected (_nr, ng, ns) ->
              Printf.printf
                "{\"ok\":false,\"kernel\":\"rocq\",\"asserted\":%d,\"derivations\":%d}\n"
                (nat_to_int_o ng) (nat_to_int_o ns);
              exit 1
          | Rocq_owlrl_core.ParseError w ->
              prerr_endline ("parse error in the " ^ which_file (nat_to_int_o w) ^ " file");
              exit 2))

let () =
  match Array.to_list Sys.argv with
  | [ _; "check"; rpath; gpath; dpath ] -> run_horn rpath gpath dpath
  | [ _; "cert"; gpath; dpath ] -> run_cert gpath dpath
  | _ -> usage ()