(* made using https://github.com/contificate/summary as a reference *)
open Util
open Primitive

(* operator associativity, for user-defined operators *)
type assoc =
  | R
  | L

module OM = Map.Make (String)

type operator_map = (int * assoc) OM.t

let fresh =
  let i = ref (-1) in
  fun () ->
    incr i;
    !i

let fresh_om () : operator_map = OM.empty
let ( >>= ) = Base.Or_error.( >>= )
let ( >>| ) = Base.Or_error.( >>| )
let ( let* ) = Base.Or_error.( >>= )
let ( let@ ) = Base.Or_error.( >>| )
let id = Fun.id
let flip = Fun.flip

(* operator, (precedence, function to get associativity) *)
let builtin_ops =
  [
    ("->", (1, ( - ) 1));
    ("::", (1, ( - ) 1));
    ("==", (2, id));
    ("/=", (2, id));
    ("&&", (3, id));
    ("||", (3, id));
    ("<", (4, id));
    (">", (4, id));
    ("<=", (4, id));
    (">=", (4, id));
    ("+", (5, id));
    ("-", (5, id));
    ("+.", (5, id));
    ("-", (5, id));
    ("*", (6, id));
    ("/", (6, id));
    ("*.", (6, id));
    ("/.", (6, id));
  ]

module Lexer : sig
  type t = {mutable tokens : Token.t list}
  type 'a result = 'a Base.Or_error.t

  val make_err : Error.t -> 'a result
  val of_string : string -> t
  val current : t -> Token.t
  val current_pos : t -> Location.t
  val advance : t -> Token.t
  val peek : t -> Token.t
  val skip : t -> am:int -> unit
  val attempt : t -> (t -> 'a result) -> (t -> 'a result) -> 'a result
  val matches : t -> Token.token -> bool

  val separated_list :
    t -> sep:Token.token -> (t -> 'a result) -> 'a list result

  val list_with_end :
    t -> (Token.token -> bool) -> (t -> 'a result) -> 'a list result

  val consume : t -> Token.token -> string -> unit result
  val consume_with_pos : t -> Token.token -> string -> Location.t result
  val consume_with : t -> (Token.token -> 'a option) -> string -> 'a result
  val consume_opt : t -> Token.token -> unit
  val gather_user_precs : t -> (operator_map * t) result
end = struct
  type t = {mutable tokens : Token.t list}
  type 'a result = 'a Base.Or_error.t

  let make_err (e : Error.t) : 'a Base.Or_error.t =
    Base.Or_error.error_string @@ Error.format_err e

  let get {tokens} = tokens

  let of_lexbuf (lexbuf : Sedlexing.lexbuf) : t =
    let rec aux acc =
      let next = Lexer.token lexbuf in
      match next with
      | (_, Token.EOF) as eof ->
        let res = List.rev (eof :: acc) in
        {tokens = res}
      | _ -> aux (next :: acc)
    in
    aux []

  let of_string (s : string) : t = Sedlexing.Utf8.from_string s |> of_lexbuf

  let current (stream : t) : Token.t =
    match stream.tokens with
    | t :: _ -> t
    | [] -> (Location.dummy_loc, Token.EOF)

  let current_pos (stream : t) : Location.t = current stream |> fst

  let advance (stream : t) : Token.t =
    match stream.tokens with
    | t :: ts ->
      stream.tokens <- ts;
      t
    | [] -> (Location.dummy_loc, Token.EOF)

  let peek (stream : t) : Token.t =
    let previous = stream.tokens in
    let next = advance stream in
    stream.tokens <- previous;
    next

  let skip (stream : t) ~am:(n : int) =
    if n < 0 then
      Error.internal "Called Lexer.skip with a negative step."
    else
      let rec aux t =
        if t <> 0 then
          let _ = advance stream in
          aux (t - 1)
      in
      aux n

  let attempt (stream : t) (p1 : t -> 'a result) (p2 : t -> 'a result) :
      'a result =
    let stream' = stream.tokens in
    match p1 stream with
    | Result.Ok _ as v -> v
    | Result.Error _ ->
      stream.tokens <- stream';
      p2 stream

  let matches (stream : t) (tok : Token.token) : bool =
    let _, next = peek stream in
    next = tok

  let separated_list (stream : t) ~(sep : Token.token) (p : t -> 'a result) :
      'a list result =
    let rec aux acc =
      let* v = p stream in
      if matches stream sep then (
        ignore (advance stream);
        v :: acc |> aux)
      else
        Result.Ok (v :: acc)
    in
    aux [] >>| List.rev

  let list_with_end (stream : t) (is_end : Token.token -> bool)
      (p : t -> 'a result) : 'a list result =
    let rec go l acc =
      let _, next = peek l in
      match next with
      | t when is_end t -> Ok (List.rev acc)
      | _ -> (
        match p l with
        | Error _ as e -> e
        | Ok v -> go l (v :: acc))
    in
    go stream []

  let consume (stream : t) (tok : Token.token) (msg : string) : unit result =
    let pos, next = advance stream in
    if next <> tok then make_err (Some pos, msg) else Ok ()

  let consume_with_pos (stream : t) (tok : Token.token) (msg : string) :
      Location.t result =
    let pos, next = advance stream in
    if next <> tok then make_err (Some pos, msg) else Ok pos

  let consume_with (stream : t) (f : Token.token -> 'a option) (msg : string) :
      'a result =
    let pos, next = advance stream in
    match f next with
    | Some v -> Ok v
    | None -> make_err (Some pos, msg)

  (* optionally consume a token. has no effect if there isn't a match. *)
  let consume_opt (stream : t) (tok : Token.token) : unit =
    let previous = stream.tokens in
    let _, next = advance stream in
    if next <> tok then stream.tokens <- previous

  let rec gather_user_precs ({tokens} : t) : ((int * assoc) OM.t * t) result =
    let open Token in
    let rec go acc ftokens = function
      | [] -> Ok (acc, List.rev ftokens)
      | ((s, ATSIGN) as h) :: rest -> (
        let l = {tokens = rest} in
        match () with
        | _ when matches l RASSOC ->
          skip ~am:1 l;
          let* op, assoc, l' = parse_assoc l R s in
          let acc' = OM.add op assoc acc in
          go acc' ftokens (get l')
        | _ when matches l LASSOC ->
          skip ~am:1 l;
          let* op, assoc, l' = parse_assoc l L s in
          let acc' = OM.add op assoc acc in
          go acc' ftokens (get l')
        | _ -> go acc (h :: ftokens) rest)
      | h :: t -> go acc (h :: ftokens) t
    in
    let@ om, r = go (fresh_om ()) [] tokens in
    (om, {tokens = r})

  and parse_assoc (stream : t) (assoc : assoc) (s : Location.t) :
      (string * (int * assoc) * t) result =
    let* p =
      consume_with stream
        (function
          | INT i -> Some i
          | _ -> None)
        "Expected precedence after assoc keyword."
    in
    if p < 1 || p > 10 then
      let loc = Location.combine s (current_pos stream) in
      make_err (Some loc, "Operator precedence must lie within range 1-10.")
    else
      let@ o =
        consume_with stream
          (function
            | OP o -> Some o
            | IDENT i -> Some i
            | _ -> None)
          "Expected operator after precedence."
      in
      (o, (p, assoc), stream)
end

let ( <|> ) l r s = Lexer.attempt s l r
let ok (v : 'a) : 'a Lexer.result = Base.Result.Ok v

module Parser = struct
  open Token

  let get_bp (t : Token.token) (om : operator_map) : int =
    match t with
    (* the parser will fail without this in cases like `f (g x)` *)
    | LPAREN | LBRACK | ARROW | TILDE | COMMA | BTICK | FORALL -> 1
    | OP op -> (
      match List.assoc_opt op builtin_ops with
      | Some (p, _) -> p
      | None -> (
        match OM.find_opt op om with
        | Some (n, _) -> n
        | None -> 9))
    | UPPER_IDENT _
    | IDENT _
    | DOT_SEP_IDENT _
    | INT _
    | TY_INT
    | FLOAT _
    | TY_FLOAT
    | CHAR _
    | TY_CHAR
    | STRING _
    | TY_STRING
    | BOOL _
    | TY_BOOL
    | UNIT
    | TY_UNIT
    | WILDCARD -> 10 (* for function application *)
    | EOF -> -2
    | _ -> -1

  (* returns operator precedence, accounting for fixity/associativity *)
  let get_bp_with_fixity (op : string) (om : operator_map) : int =
    match List.assoc_opt op builtin_ops with
    | Some (p, f) -> f p
    | None -> (
      match OM.find_opt op om with
      | Some (n, R) -> n - 1
      | Some (n, L) -> n
      | None -> 8)

  let parse_upper_ident (l : Lexer.t) : string Lexer.result =
    Lexer.consume_with l
      (function
        | UPPER_IDENT i -> Some i
        | _ -> None)
      "Expected an uppercase identifier."

  let parse_lower_ident (l : Lexer.t) : string Lexer.result =
    Lexer.consume_with l
      (function
        | IDENT i -> Some i
        | _ -> None)
      "Expected a lowercase identifier."

  let parse_ident (l : Lexer.t) : string Lexer.result =
    Lexer.consume_with l
      (function
        | IDENT i | UPPER_IDENT i -> Some i
        | _ -> None)
      "Expected an identifier."

  let parse_user_op (l : Lexer.t) : string Lexer.result =
    Lexer.consume_with l
      (function
        | OP o -> Some o
        | _ -> None)
      "Expected a user-defined operator."

  let rec parse_args (l : Lexer.t) : located_pattern list Lexer.result =
    Lexer.list_with_end l
      (function
        | WILDCARD
        | LBRACK
        | LPAREN
        | IDENT _
        | INT _
        | FLOAT _
        | STRING _
        | CHAR _
        | BOOL _
        | ATSIGN
        | UPPER_IDENT _
        | UNIT -> false
        | _ -> true)
      parse_pattern

  and parse_pattern (l : Lexer.t) : located_pattern Lexer.result =
    match Lexer.advance l with
    | s, LBRACK ->
      let* r =
        ( (fun l ->
            let@ e =
              Lexer.consume_with_pos l RBRACK
                "Expected ']' to end empty list constructor."
            in
            (Location.combine s e, PVar "Nil"))
        <|> fun l ->
          let* es = Lexer.separated_list l ~sep:SEMI parse_pattern in
          let@ e =
            Lexer.consume_with_pos l RBRACK "Expected ']' to end list."
          in
          let loc = Location.combine s e in
          List.fold_right
            (fun n acc -> (loc, PCtor ("::", [n; acc])))
            (List.tl es) (List.hd es) )
          l
      in
      parse_pbop l r
    | s, LPAREN -> (
      match Lexer.current l with
      | _, UPPER_IDENT i ->
        Lexer.skip ~am:1 l;
        let* ps =
          ( (fun l -> Lexer.list_with_end l (( = ) RPAREN) parse_pattern)
          <|> fun _ -> ok [] )
            l
        in
        let* e =
          Lexer.consume_with_pos l RPAREN
            "Expected ')' to end parenthesised pattern."
        in
        parse_pbop l (Location.combine s e, PCtor (i, ps))
      | _ -> (
        let* l' = parse_pattern l in
        match Lexer.current l with
        | _, RPAREN ->
          Lexer.skip ~am:1 l;
          parse_pbop l l'
        | pos, tok ->
          Lexer.make_err
            ( Some pos,
              Printf.sprintf "Expected ')', but got '%s'." (Token.show tok) )))
    | s, WILDCARD -> parse_pbop l (s, PWild)
    | s, IDENT i -> parse_pbop l (s, PVar i)
    | s, UPPER_IDENT i -> parse_pbop l (s, PCtor (i, []))
    | s, INT i -> parse_pbop l (s, PConst (Int i))
    | s, FLOAT i -> parse_pbop l (s, PConst (Float i))
    | s, STRING i -> parse_pbop l (s, PConst (String i))
    | s, CHAR i -> parse_pbop l (s, PConst (Char i))
    | s, BOOL i -> parse_pbop l (s, PConst (Bool i))
    | s, UNIT -> parse_pbop l (s, PConst Unit)
    | s, TY_INT -> parse_pbop l (s, PTypeLit PInt)
    | s, TY_FLOAT -> parse_pbop l (s, PTypeLit PFloat)
    | s, TY_STRING -> parse_pbop l (s, PTypeLit PString)
    | s, TY_CHAR -> parse_pbop l (s, PTypeLit PChar)
    | s, TY_BOOL -> parse_pbop l (s, PTypeLit PBool)
    | s, TY_UNIT -> parse_pbop l (s, PTypeLit PUnit)
    | s, UNIVERSE ->
      let* p =
        ( (fun l ->
            let e = Lexer.current_pos l in
            let* n =
              Lexer.consume_with l
                (function
                  | INT i -> Some i
                  | _ -> None)
                "Expected an integer for the universe level."
            in
            let loc = Location.combine s e in
            if n < 0 then
              Lexer.make_err
                ( Some loc,
                  Printf.sprintf
                    "Expected a natural number for universe level, but got \
                     '%d'."
                    n )
            else
              ok (loc, PTypeLit (PUni n)))
        <|> fun _ -> ok @@ (s, PTypeLit (PUni 0)) )
          (* α : Type ⇒ α : Type 0 *)
          l
      in
      parse_pbop l p
    | pos, tok ->
      Lexer.make_err
        ( Some pos,
          Printf.sprintf "Expected pattern, but got '%s'." (Token.show tok) )

  and parse_pbop (l : Lexer.t) ((s, _) as left : located_pattern) :
      located_pattern Lexer.result =
    ( ( (fun l ->
          let* o =
            Lexer.consume_with l
              (function
                | OP o -> Some o
                | ARROW -> Some "->"
                | _ -> None)
              "Expected operator."
          in
          let@ ((e, _) as next) = parse_pattern l in
          (Location.combine s e, PCtor (o, [left; next])))
      <|> fun l ->
        let* _ = Lexer.consume l COMMA "Expected comma for a tuple pattern." in
        let@ ((e, _) as r) = parse_pattern l in
        (Location.combine s e, PTuple (left, r)) )
    <|> fun _ -> ok left )
      l

  (* https://www.youtube.com/watch?v=2l1Si4gSb9A *)
  let rec parse_expr (l : Lexer.t) (limit : int) (om : operator_map) :
      Ast.located_expr Lexer.result =
    let* ((s, _) as left) = nud l om in
    let rec go lf =
      if Lexer.current l |> snd |> flip get_bp om > limit then
        let _, op_tok = Lexer.advance l in
        let* res = led l lf s op_tok om in
        go res
      else
        ok lf
    in
    go left

  and nud (l : Lexer.t) (om : operator_map) : Ast.located_expr Lexer.result =
    match Lexer.advance l with
    | s, WILDCARD -> ok (s, Ast.Hole) (* e.g. id _ 10 *)
    | s, INT i -> ok (s, Ast.Const (Int i))
    | s, FLOAT f -> ok (s, Ast.Const (Float f))
    | s, CHAR c -> ok (s, Ast.Const (Char c))
    | s, STRING str -> ok (s, Ast.Const (String str))
    | s, BOOL b -> ok (s, Ast.Const (Bool b))
    | s, UNIT -> ok (s, Ast.Const Unit)
    | s, TY_INT -> ok (s, Ast.TypeLit PInt)
    | s, TY_FLOAT -> ok (s, Ast.TypeLit PFloat)
    | s, TY_STRING -> ok (s, Ast.TypeLit PString)
    | s, TY_CHAR -> ok (s, Ast.TypeLit PChar)
    | s, TY_BOOL -> ok (s, Ast.TypeLit PBool)
    | s, TY_UNIT -> ok (s, Ast.TypeLit PUnit)
    | s, UNIVERSE ->
      ( (fun l ->
          let e = Lexer.current_pos l in
          let* n =
            Lexer.consume_with l
              (function
                | INT i -> Some i
                | _ -> None)
              "Expected an integer for the universe level."
          in
          let loc = Location.combine s e in
          if n < 0 then
            Lexer.make_err
              ( Some loc,
                Printf.sprintf
                  "Expected a natural number for universe level, but got '%d'."
                  n )
          else
            ok (loc, Ast.TypeLit (PUni n)))
      <|> fun _ -> ok @@ (s, Ast.TypeLit (PUni 0)) )
        (* α ~ U ⇒ α ~ U 0 *)
        l
    | s, IDENT i -> ok (s, Ast.Var (Ident i))
    | s, UPPER_IDENT i ->
      ( (fun l ->
          let@ e, fields = parse_record_fields l om in
          (Location.combine s e, Ast.RCons (i, fields)))
      <|> fun _ -> ok (s, Ast.Var (Udc i)) )
        l
    | s, DOT_SEP_IDENT (i, is) -> ok (s, Ast.Var (AccessIdent (i, is)))
    | s, LET -> parse_let l om s
    | s, IF -> parse_if l om s
    | s, FUN -> parse_lam l om s
    | s, MATCH -> parse_match l om s
    | s, FORALL -> parse_forall l om s
    | s, LBRACE ->
      ( (fun l -> parse_binding l ~icit:Imp s om) <|> fun l ->
        let* ru = parse_record_update l om in
        let@ e =
          Lexer.consume_with_pos l RBRACE "Expected '}' to end record update."
        in
        (Location.combine s e, ru) )
        l
    | s, LBRACK ->
      ( (fun l ->
          let@ e =
            Lexer.consume_with_pos l RBRACK
              "Expected ']' to end empty list constructor."
          in
          let loc = Location.combine s e in
          (loc, Ast.Var (Udc "Nil")))
      <|> fun l ->
        let* es =
          Lexer.separated_list l ~sep:SEMI (fun e -> parse_expr e 0 om)
        in
        let@ e = Lexer.consume_with_pos l RBRACK "Expected ']' to end list." in
        let loc = Location.combine s e in
        let op = (loc, Ast.Var (Ident "::")) in
        List.fold_right
          (fun n acc -> (loc, Ast.Ap (0, (loc, Ast.Ap (0, op, n)), acc)))
          (List.tl es) (List.hd es) )
        l
    | s, LPAREN ->
      ( ( (fun l ->
            let* o = parse_user_op l in
            let@ e =
              Lexer.consume_with_pos l RPAREN
                "Expected ')' after prefix operator."
            in
            let loc = Location.combine s e in
            (loc, Ast.Var (Ident o)))
        <|> fun l -> parse_binding l ~icit:Exp s om )
      <|> fun l ->
        let* _, expr = parse_expr l 0 om in
        match Lexer.current l with
        | e, RPAREN ->
          Lexer.skip ~am:1 l;
          ok (Location.combine s e, expr)
        | pos, tok ->
          Lexer.make_err
            ( Some pos,
              Printf.sprintf
                "Expected either ')' to end grouped expression or ',' to start \
                 tuple expression, but got '%s'."
                (Token.show tok) ) )
        l
    | s, OP o ->
      let@ ((e, _) as v) = parse_expr l (get_bp_with_fixity o om) om in
      (Location.combine s e, Ast.Ap (0, (s, Ast.Var (Ident o)), v))
    | pos, tok ->
      Lexer.make_err
        ( Some pos,
          Printf.sprintf "Unexpected token while parsing left: %s"
            (Token.show tok) )

  and led (l : Lexer.t) (left : Ast.located_expr) (s : Location.t)
      (op : Token.token) (om : operator_map) : Ast.located_expr Lexer.result =
    let@ expr =
      match op with
      | OP o ->
        let@ r = parse_expr l (get_bp_with_fixity o om) om in
        let loc, _ = left in
        let op = (loc, Ast.Var (Ident o)) in
        Ast.Ap (0, (loc, Ast.Ap (0, op, left)), r)
      | ARROW ->
        let@ r = parse_expr l 0 om in
        Ast.Pi (("_", Exp), left, r)
      | TILDE ->
        let@ r = parse_expr l 0 om in
        Ast.Annot (left, r)
      | COMMA ->
        let@ r = parse_expr l 0 om in
        Ast.Tuple (left, r)
      | BTICK ->
        let* f = parse_lower_ident l in
        let* e =
          Lexer.consume_with_pos l BTICK
            "Expected another '`' for an infix function application."
        in
        let@ r = parse_expr l (get_bp_with_fixity f om) om in
        let loc = Location.combine (fst left) e in
        let f = (loc, Ast.Var (Ident f)) in
        Ast.Ap (0, (loc, Ast.Ap (0, f, left)), r)
      | WILDCARD -> ok (Ast.Ap (0, left, (s, Ast.Hole)))
      | INT i -> ok (Ast.Ap (0, left, (s, Ast.Const (Int i))))
      | FLOAT f -> ok (Ast.Ap (0, left, (s, Ast.Const (Float f))))
      | CHAR c -> ok (Ast.Ap (0, left, (s, Ast.Const (Char c))))
      | STRING str -> ok (Ast.Ap (0, left, (s, Ast.Const (String str))))
      | BOOL b -> ok (Ast.Ap (0, left, (s, Ast.Const (Bool b))))
      | UNIT -> ok (Ast.Ap (0, left, (s, Ast.Const Unit)))
      | TY_INT -> ok (Ast.Ap (0, left, (s, Ast.TypeLit PInt)))
      | TY_FLOAT -> ok (Ast.Ap (0, left, (s, Ast.TypeLit PFloat)))
      | TY_STRING -> ok (Ast.Ap (0, left, (s, Ast.TypeLit PString)))
      | TY_CHAR -> ok (Ast.Ap (0, left, (s, Ast.TypeLit PChar)))
      | TY_BOOL -> ok (Ast.Ap (0, left, (s, Ast.TypeLit PBool)))
      | TY_UNIT -> ok (Ast.Ap (0, left, (s, Ast.TypeLit PUnit)))
      | IDENT i ->
        let r = (s, Ast.Var (Ident i)) in
        ok @@ Ast.Ap (0, left, r)
      | UPPER_IDENT i ->
        let* r =
          ( (fun l ->
              let@ e, fields = parse_record_fields l om in
              (Location.combine s e, Ast.RCons (i, fields)))
          <|> fun _ -> ok (s, Ast.Var (Udc i)) )
            l
        in
        ok @@ Ast.Ap (0, left, r)
      | DOT_SEP_IDENT (i, is) ->
        let r = (s, Ast.Var (AccessIdent (i, is))) in
        ok @@ Ast.Ap (0, left, r)
      | UNIVERSE ->
        let@ r =
          ( (fun l ->
              let e = Lexer.current_pos l in
              let* n =
                Lexer.consume_with l
                  (function
                    | INT i -> Some i
                    | _ -> None)
                  "Expected an integer for the universe level."
              in
              let loc = Location.combine s e in
              if n < 0 then
                Lexer.make_err
                  ( Some loc,
                    Printf.sprintf
                      "Expected a natural number for universe level, but got \
                       '%d'."
                      n )
              else
                ok (loc, Ast.TypeLit (PUni n)))
          <|> fun _ -> ok @@ (s, Ast.TypeLit (PUni 0)) )
            (* e ~ U ⇒ e ~ U 0 *)
            l
        in
        Ast.Ap (0, left, r)
      | LBRACK ->
        let@ r =
          ( (fun l ->
              let@ e =
                Lexer.consume_with_pos l RBRACK
                  "Expected ']' to end empty list constructor."
              in
              let loc = Location.combine s e in
              (loc, Ast.Var (Udc "Nil")))
          <|> fun l ->
            let* es =
              Lexer.separated_list l ~sep:SEMI (fun e -> parse_expr e 0 om)
            in
            let@ e =
              Lexer.consume_with_pos l RBRACK "Expected ']' to end list."
            in
            let loc = Location.combine s e in
            let op = (loc, Ast.Var (Ident "::")) in
            List.fold_right
              (fun n acc -> (loc, Ast.Ap (0, (loc, Ast.Ap (0, op, n)), acc)))
              (List.tl es) (List.hd es) )
            l
        in
        Ast.Ap (0, left, r)
      | LBRACE ->
        let@ r =
          ( (fun l -> parse_binding ~icit:Imp l s om) <|> fun l ->
            let* ru = parse_record_update l om in
            let@ e =
              Lexer.consume_with_pos l RBRACE
                "Expected '}' to end record update."
            in
            (Location.combine s e, ru) )
            l
        in
        Ast.Ap (0, left, r)
      | LPAREN ->
        let s = Lexer.current_pos l in
        ( ( (fun l ->
              let* o = parse_user_op l in
              let@ e =
                Lexer.consume_with_pos l RPAREN
                  "Expected ')' after prefix operator."
              in
              let loc = Location.combine s e in
              Ast.Ap (0, left, (loc, Ast.Var (Ident o))))
          <|> fun l ->
            let@ r = parse_binding ~icit:Exp l s om in
            Ast.Ap (0, left, r) )
        <|> fun l ->
          let* _, expr = parse_expr l 0 om in
          match Lexer.current l with
          | e, RPAREN ->
            Lexer.skip ~am:1 l;
            ok @@ Ast.Ap (0, left, (Location.combine s e, expr))
          | pos, tok ->
            Lexer.make_err
              ( Some pos,
                Printf.sprintf
                  "Expected either ')' to end grouped expression or ',' to \
                   start tuple expression, but got '%s'."
                  (Token.show tok) ) )
          l
      | op ->
        Lexer.make_err
          ( Some s,
            Printf.sprintf "Expected binary operator, got '%s'." (Token.show op)
          )
    in
    (Location.combine s (Lexer.current_pos l), expr)

  and parse_binding (l : Lexer.t) ~(icit : icit) (s : Location.t)
      (om : operator_map) : Ast.located_expr Lexer.result =
    let r_paren =
      match icit with
      | Exp -> RPAREN
      | Imp -> RBRACE
    in
    let* is =
      ( (fun l -> Lexer.separated_list l ~sep:COMMA parse_ident) <|> fun l ->
        let@ i = parse_ident l in
        [i] )
        l
    in
    let* _ =
      Lexer.consume l COLON
        "Expected a ':' between a type and identifier in a type binding."
    in
    let* l' = parse_expr l 0 om in
    let* _ =
      Lexer.consume l r_paren "Expected a ')' or '}' to end a type binding."
    in
    let* _ = Lexer.consume l ARROW "Expected an '->' after a type binding." in
    let@ ((e, _) as r) = parse_expr l 0 om in
    let loc = Location.combine s e in
    List.fold_right (fun n acc -> (loc, Ast.Pi ((n, icit), l', acc))) is r

  and parse_type_ident (l : Lexer.t) (om : operator_map) :
      (string * Ast.located_expr) Lexer.result =
    let s = Lexer.current_pos l in
    ( (fun l ->
        (* ∀ a. ⇒ ∀ (a ~ U). *)
        let@ i = parse_ident l in
        let t = (s, Ast.TypeLit (PUni 0)) in
        (i, t))
    <|> fun l ->
      let* _ =
        Lexer.consume l LPAREN
          "Expected a '(' to begin a type identifier with an explicit type."
      in
      let* i = parse_ident l in
      let* _ =
        Lexer.consume l TILDE
          "Expected a '~' to separate the identifier and type."
      in
      let* t = parse_expr l 0 om in
      let@ _ =
        Lexer.consume l RPAREN
          "Expected a ')' to end a type identifier with an explicit type."
      in
      (i, t) )
      l

  and parse_forall (l : Lexer.t) (om : operator_map) (s : Location.t) :
      Ast.located_expr Lexer.result =
    let* binds = Lexer.list_with_end l (( = ) DOT) (flip parse_type_ident om) in
    let* _ =
      Lexer.consume l DOT
        "Expected a '.' to separate the binders in a forall expression."
    in
    let@ ((e, _) as t) = parse_expr l 0 om in
    let loc = Location.combine s e in
    List.fold_right
      (fun (i, t) acc ->
        let bind = (i, Imp) in
        (loc, Ast.Pi (bind, t, acc)))
      binds t

  and parse_record_fields (l : Lexer.t) (om : operator_map) :
      (Location.t * (string * Ast.located_expr) list) Lexer.result =
    let* _ =
      Lexer.consume l LBRACE "Expected a '{' to begin a record constructor."
    in
    let parse_field l =
      ( (fun l ->
          let* id = parse_lower_ident l in
          let* _ =
            Lexer.consume l ASSIGNMENT
              "Expected a ':=' to separate identifier and expression in record \
               construction."
          in
          let@ v = parse_expr l 0 om in
          (id, v))
      <|>
      (*
         record punning; 
         cons { x₁; ...; xₙ } ⇒ cons { x₁ = x₁; ...; xₙ = xₙ }
         checking if it's a valid field occurs in elaboration.
      *)
      fun l ->
        let s = Lexer.current_pos l in
        let@ id = parse_lower_ident l in
        let v = (s, Ast.Var (Ident id)) in
        (id, v) )
        l
    in
    let* fields = Lexer.separated_list l ~sep:SEMI parse_field in
    let@ e =
      Lexer.consume_with_pos l RBRACE
        "Expected a '}' to end a record constructor."
    in
    (e, fields)

  and parse_record_update (l : Lexer.t) (om : operator_map) :
      Ast.expr Lexer.result =
    let* i = parse_lower_ident l in
    let* _ =
      Lexer.consume l WHERE
        "Expected 'where' after identifier in record update."
    in
    let parse_update l om =
      ( (fun l ->
          let* id = parse_lower_ident l in
          let* _ =
            Lexer.consume l ASSIGNMENT
              "Expected a ':=' to separate identifier and expression in record \
               update."
          in
          let@ v = parse_expr l 0 om in
          (Ast.Assign, id, v))
      <|> fun l ->
        let* id = parse_lower_ident l in
        let* _ =
          Lexer.consume l RECORD_FUN
            "Expected a '=@' to separate identifier and expression in record \
             update."
        in
        let@ f = parse_expr l 0 om in
        (Ast.Apply, id, f) )
        l
    in
    let@ fields = Lexer.separated_list l ~sep:SEMI (flip parse_update om) in
    Ast.RUpdate (i, fields)

  and parse_let (l : Lexer.t) (om : operator_map) (s : Location.t) :
      Ast.located_expr Lexer.result =
    let* p = parse_pattern l in
    let* ty =
      match Lexer.current l with
      | _, COLON ->
        Lexer.skip ~am:1 l;
        let* ty = parse_expr l 0 om in
        let@ _ =
          Lexer.consume l EQ "Expected '=' after type in let-expression."
        in
        Some ty
      | _, ASSIGNMENT ->
        Lexer.skip ~am:1 l;
        ok None
      | pos, tok ->
        Lexer.make_err
          ( Some pos,
            Printf.sprintf "Unexpected token in let-expression: %s"
              (Token.show tok) )
    in
    let* expr = parse_expr l 0 om in
    let* e =
      Lexer.consume_with_pos l IN "Expected 'in' to end let-expression."
    in
    let@ n = parse_expr l 0 om in
    (Location.combine s e, Ast.Let (p, ty, expr, n))

  and parse_if (l : Lexer.t) (om : operator_map) (s : Location.t) :
      Ast.located_expr Lexer.result =
    let* cond = parse_expr l 0 om in
    let* _ =
      Lexer.consume l THEN
        "Expected 'then' keyword after if statement condition."
    in
    let* texpr = parse_expr l 0 om in
    let* _ =
      Lexer.consume l ELSE "Expected 'else' keyword to begin alternate branch."
    in
    let@ ((e, _) as fexpr) = parse_expr l 0 om in
    (Location.combine s e, Ast.If (cond, texpr, fexpr))

  and parse_lam (l : Lexer.t) (om : operator_map) (s : Location.t) :
      Ast.located_expr Lexer.result =
    let* args = parse_args l in
    let* _ = Lexer.consume l DOT "Expected '.' after lambda arguments." in
    let@ b = parse_expr l 0 om in
    let loc = Location.combine s (Lexer.current_pos l) in
    List.fold_right (fun n acc -> (loc, Ast.Lam (n, acc))) args b

  and parse_match (l : Lexer.t) (om : operator_map) (s : Location.t) :
      Ast.located_expr Lexer.result =
    let* expr = parse_expr l 0 om in
    let* _ = Lexer.consume l TO "Expected 'to' after match subject." in
    let go l =
      let* p = parse_pattern l in
      let* wb =
        match Lexer.current l with
        | _, WHEN ->
          Lexer.skip ~am:1 l;
          let@ e = parse_expr l 0 om in
          Some e
        | _ -> ok None
      in
      let* _ =
        Lexer.consume l F_ARROW "Expected '=>' or '⇒' after match pattern."
      in
      let@ e = parse_expr l 0 om in
      (p, wb, e)
    in
    Lexer.consume_opt l PIPE;
    let@ branches = Lexer.separated_list l ~sep:PIPE go in
    (Location.combine s (Lexer.current_pos l), Ast.Match (expr, branches))

  let rec parse_definition (l : Lexer.t) (om : operator_map) :
      Ast.located_definition Lexer.result =
    match Lexer.current l with
    | _, DEC -> parse_dec l om
    | _, DEF -> parse_def l om
    | pos, tok ->
      Lexer.make_err
        ( Some pos,
          Printf.sprintf
            "Expected 'dec' or 'def' keyword to begin a definition, but got \
             '%s'."
            (Token.show tok) )

  and parse_def (l : Lexer.t) (om : operator_map) :
      Ast.located_definition Lexer.result =
    let* s = Lexer.consume_with_pos l DEF "Expected 'def' keyword." in
    let* n = parse_definition_ident l in
    let* args = parse_args l in
    let* when_block =
      match Lexer.current l with
      | _, COLON ->
        Lexer.skip l ~am:1;
        let* _ = Lexer.consume l WHEN "Expected 'when' after ':' in def." in
        let* block = parse_expr l 0 om in
        let@ _ = Lexer.consume l EQ "Expected '=' after when block." in
        Some block
      | _, ASSIGNMENT ->
        Lexer.skip l ~am:1;
        ok None
      | pos, tok ->
        Lexer.make_err
          ( Some pos,
            Printf.sprintf
              "Expected ':' or ':=' after definition arguments, but got '%s'."
              (Token.show tok) )
    in
    let* ((loc, _) as body) = parse_expr l 0 om in
    let@ e, with_block =
      ( (fun l ->
          let* _ =
            Lexer.consume l WITH
              "Expected 'with' keyword to begin local function definitions."
          in
          let* defs =
            Lexer.list_with_end l (( = ) END) (flip parse_definition om)
          in
          let@ e =
            Lexer.consume_with_pos l END
              "Expected 'end' keyword after local definitions."
          in
          (e, defs))
      <|> fun _ -> ok (loc, []) )
        l
    in
    (Location.combine s e, Ast.Def (n, args, when_block, body, with_block))

  and parse_dec (l : Lexer.t) (om : operator_map) :
      Ast.located_definition Lexer.result =
    let* s = Lexer.consume_with_pos l DEC "Expected 'dec' keyword." in
    let* n = parse_definition_ident l in
    let* _ = Lexer.consume l COLON "Expected ':' after 'dec' keyword." in
    let@ ((e, _) as t) = parse_expr l 0 om in
    (Location.combine s e, Ast.Dec (n, t))

  and parse_definition_ident (l : Lexer.t) : string Lexer.result =
    match Lexer.advance l with
    | _, IDENT i -> ok i
    | _, LPAREN ->
      let* i = parse_user_op l in
      let@ _ =
        Lexer.consume l RPAREN "Expected ')' after operator identifier."
      in
      i
    | pos, tok ->
      Lexer.make_err
        ( Some pos,
          Printf.sprintf "Expected identifier or operator, but got '%s'."
            (Token.show tok) )

  let rec parse_tydecl (l : Lexer.t) (om : operator_map) :
      Ast.located_ty_decl Lexer.result =
    let@ s, ident, ty =
      ( ((fun l -> parse_alias l om) <|> fun l -> parse_data l om) <|> fun l ->
        parse_record l om )
        l
    in
    let e = Lexer.current l |> fst in
    (Location.combine s e, (ident, ty))

  and parse_alias (l : Lexer.t) (om : operator_map) :
      (Location.t * string * Ast.tdecl_type) Lexer.result =
    let* s = Lexer.consume_with_pos l ALIAS "Expected alias keyword." in
    let* ident =
      ( (fun l -> parse_upper_ident l) <|> fun l ->
        let* _ =
          Lexer.consume l LPAREN "Expected '(' to begin operator identifier."
        in
        let* i = parse_user_op l in
        let@ _ =
          Lexer.consume l RPAREN "Expected ')' to end operator identifier."
        in
        i )
        l
    in
    let* _ =
      Lexer.consume l ASSIGNMENT "Expected a ':=' for type assignment."
    in
    let@ t = parse_expr l 0 om in
    (s, ident, Ast.Alias t)

  and parse_data (l : Lexer.t) (om : operator_map) :
      (Location.t * string * Ast.tdecl_type) Lexer.result =
    let* s = Lexer.consume_with_pos l DATA "Expected union keyword." in
    let* ident =
      ( (fun l -> parse_upper_ident l) <|> fun l ->
        let* _ =
          Lexer.consume l LPAREN "Expected '(' to begin operator identifier."
        in
        let* i = parse_user_op l in
        let@ _ =
          Lexer.consume l RPAREN "Expected ')' to end operator identifier."
        in
        i )
        l
    in
    let* _ = Lexer.consume l COLON "Expected a ':' before type signature." in
    let* tsig = parse_expr l 0 om in
    let* _ = Lexer.consume l EQ "Expected a '=' after type signature." in
    Lexer.consume_opt l PIPE;
    let parse_variant l om =
      let* ident =
        match Lexer.current l with
        | _, LPAREN ->
          Lexer.skip ~am:1 l;
          let* i = parse_user_op l in
          Log.dbg None (Printf.sprintf "user_op := %s\n" i);
          let@ _ =
            Lexer.consume l RPAREN "Expected a ')' to end operator variant."
          in
          i
        | _ -> parse_upper_ident l
      in
      let* _ =
        Lexer.consume l COLON "Expected a ':' after variant identifier."
      in
      let@ e = parse_expr l 0 om in
      (ident, e)
    in
    let@ variants = Lexer.separated_list l ~sep:PIPE (flip parse_variant om) in
    (s, ident, Ast.Variant (tsig, variants))

  and parse_record (l : Lexer.t) (om : operator_map) :
      (Location.t * string * Ast.tdecl_type) Lexer.result =
    let* s = Lexer.consume_with_pos l RECORD "Expected record keyword." in
    let* ident = parse_upper_ident l in
    let* _ =
      Lexer.consume l COLON "Expected a ':' before record type signature."
    in
    let* t = parse_expr l 0 om in
    let* _ = Lexer.consume l EQ "Expected a '=' after record type signature." in
    let* _ =
      Lexer.consume l CONSTRUCTOR
        "Expected 'constructor' keyword to declare record constructor."
    in
    let* cons = parse_upper_ident l in
    let parse_field l om =
      let* id = parse_lower_ident l in
      let* _ =
        Lexer.consume l COLON
          "Expected a ':' to separate the field name and type."
      in
      let@ ty = parse_expr l 0 om in
      (id, ty)
    in
    Lexer.consume_opt l PIPE;
    let@ fields = Lexer.separated_list l ~sep:PIPE (flip parse_field om) in
    (s, ident, Ast.Record (cons, t, fields))

  let parse_module (l : Lexer.t) : string Lexer.result =
    let* _ = Lexer.consume l MODULE "Expected the 'module' keyword." in
    parse_upper_ident l

  let rec parse_import (l : Lexer.t) : located_import Lexer.result =
    let* s = Lexer.consume_with_pos l IMPORT "Expected the 'import' keyword." in
    let* name = parse_upper_ident l in
    let@ cond, e =
      if Lexer.matches l WITH || Lexer.matches l WITHOUT then
        let@ c, e = parse_import_cond l in
        (Some c, e)
      else
        ok (None, Lexer.current_pos l)
    in
    (Location.combine s e, (Ident name, cond))

  and parse_import_cond (l : Lexer.t) : (import_cond * Location.t) Lexer.result
      =
    let* cond_type =
      Lexer.consume_with l
        (function
          | WITH -> Some true
          | WITHOUT -> Some false
          | _ -> None)
        "Expected an import condition."
    in
    let@ values, e =
      match Lexer.advance l with
      | _, LPAREN ->
        let* contents = Lexer.separated_list l ~sep:COMMA parse_ident in
        let@ p =
          Lexer.consume_with_pos l RPAREN
            "Expected a ')' to end the import condition."
        in
        (List.map (fun i -> Ident i) contents, p)
      | p, IDENT i | p, UPPER_IDENT i -> ok ([Ident i], p)
      | pos, tok ->
        Lexer.make_err
          ( Some pos,
            Printf.sprintf
              "Expected identifier or comma-separated list of identifiers, but \
               got '%s'."
              (Token.show tok) )
    in
    if cond_type then (CWith values, e) else (CWithout values, e)

  let parse_toplvl (l : Lexer.t) (om : operator_map) : Ast.top_lvl Lexer.result
      =
    ( ( ( (fun l ->
            let@ i = parse_import l in
            Ast.TImport i)
        <|> fun l ->
          let@ t = parse_tydecl l om in
          Ast.TTyDecl t )
      <|> fun l ->
        let@ d = parse_dec l om in
        Ast.TDef d )
    <|> fun l ->
      let@ d = parse_def l om in
      Ast.TDef d )
      l

  let parse_program (l : Lexer.t) : Ast.program Lexer.result =
    let* om, l = Lexer.gather_user_precs l in
    let* mod' = parse_module l in
    let@ prog = Lexer.list_with_end l (( = ) EOF) (flip parse_toplvl om) in
    let imports =
      List.filter_map
        (function
          | Ast.TImport i -> Some i
          | _ -> None)
        prog
    in
    let tydecls =
      List.filter_map
        (function
          | Ast.TTyDecl t -> Some t
          | _ -> None)
        prog
    in
    let body =
      List.filter_map
        (function
          | Ast.TDef d -> Some d
          | _ -> None)
        prog
    in
    (mod', imports, tydecls, body)
end
