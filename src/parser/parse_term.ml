module A = Ast_term
module P = Parser_comb
open P.Infix

let is_alpha = function
  | 'a' .. 'z' | 'A' .. 'Z' -> true
  | _ -> false

let is_num = function
  | '0' .. '9' -> true
  | _ -> false

let is_alphanum = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' -> true
  | _ -> false

let id : string P.t =
  P.chars_fold_transduce `Start ~f:(fun st c ->
      match st, c with
      | `Start, c when is_alpha c -> `Yield (`Inside, c)
      | `Inside, c when is_alphanum c -> `Yield (`Inside, c)
      | `Start, _ -> `Fail "expected identifier"
      | `Inside, _ -> `Stop)
  >|= snd

let int : string P.t =
  P.chars_fold_transduce `Start ~f:(fun st c ->
      match st, c with
      | `Start, '-' -> `Yield (`Post_neg, c)
      | (`Start | `Post_neg | `Inside), c when is_num c -> `Yield (`Inside, c)
      | `Start, _ -> `Fail "expected integer"
      | `Post_neg, _ -> `Fail "expected a number after '-'"
      | `Inside, _ -> `Stop)
  >|= snd

let with_loc (p : 'a P.t) : ('a * A.loc) P.t =
  let+ start = P.pos and+ x = p and+ end_ = P.pos in
  let loc = A.mk_loc ~start ~end_ in
  x, loc

(* TODO: also skip comments *)
let skip_white : unit P.t = P.skip_white

let p_var : A.term P.t =
  let+ name, loc = with_loc id in
  A.mk_var ~loc name

let p_int : A.term P.t =
  let+ x, loc = with_loc int in
  A.mk_int ~loc x

(* main parser *)
let rec p_term () : A.term P.t =
  P.suspend @@ fun () ->
  P.skip_white
  *> (P.try_or_l ~msg:"expected term"
     @@ List.flatten
          [
            [
              ( P.lookahead_ignore (P.guard (String.equal "let") id),
                let+ _id_let, loc = with_loc id
                and+ x = skip_white *> id
                and+ _ = skip_white *> P.string ":="
                and+ t = p_term ()
                and+ _ = skip_white *> P.string "in"
                and+ bod = p_term () in
                assert (_id_let = "let");
                (* TODO: allow [let x : _ := t in bod] *)
                let x = A.var x in
                A.mk_let ~loc [ x, t ] bod );
            ];
            p_term_atomic_cases () ~f:(fun t -> p_term_apply t []);
          ])

and p_term_atomic_cases ~f () : _ list =
  [
    P.lookahead_ignore id, p_var >>= f;
    P.lookahead_ignore int, p_int >>= f;
    ( P.lookahead_ignore (P.char '('),
      P.char '(' *> p_term () <* skip_white *> P.char ')' >>= f );
  ]

and p_term_atomic ?else_ ~f () =
  P.suspend @@ fun () ->
  P.try_or_l ?else_ ~msg:"expected atomic term" @@ p_term_atomic_cases ~f ()

(* TODO: handle infix symbols, with a table (sym -> precedence * parser).
   Start by registering "=" and "->" in there. *)
(* TODO: handle lambda and pi *)

(* parse application of [t] to 0 or more arguments *)
and p_term_apply t args : A.term P.t =
  P.suspend @@ fun () ->
  let ret = P.suspend @@ fun () -> P.return @@ A.mk_app t (List.rev args) in
  skip_white
  *> (P.try_or_l ~else_:ret
     @@ List.flatten
          [
            [
              P.eoi, ret;
              ( P.lookahead_ignore (P.guard (fun s -> s = "let" || s = "in") id),
                (* if we meet some keyword, we stop *)
                ret );
            ];
            p_term_atomic_cases () ~f:(fun a -> p_term_apply t (a :: args));
          ])

let p = p_term ()
let of_string s = P.parse_string_e p s
let of_string_exn s = P.parse_string_exn p s
let of_string_l s = P.parse_string_e (P.many p) s
let of_string_l_exn s = P.parse_string_exn (P.many p) s
