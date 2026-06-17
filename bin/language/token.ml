open Util

type t = Location.t * token

and token =
  | INT of int
  | TY_INT
  | FLOAT of float
  | TY_FLOAT
  | STRING of string
  | TY_STRING
  | CHAR of char
  | TY_CHAR
  | BOOL of bool
  | TY_BOOL
  | UNIT
  | TY_UNIT
  | TY_ATOM
  | IDENT of string
  | UPPER_IDENT of string
  | DOT_SEP_IDENT of string * string list
  | OP of string
  | IMPOSSIBLE
  | WHEN
  | WHERE
  | WITH
  | MATCH
  | TO
  | WITHOUT
  | RASSOC
  | LASSOC
  | IF
  | THEN
  | ELSE
  | DEC
  | TYPE
  | DEF
  | FUN
  | LET
  | IN
  | END
  | MODULE
  | IMPORT
  | ALIAS
  | DATA
  | RECORD
  | CONSTRUCTOR
  | UNIVERSE
  | FORALL
  | STAR
  | PIPE
  | LBRACE
  | RBRACE
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | SEMI
  | COLON
  | EQ
  | ASSIGNMENT
  | ARROW
  | F_ARROW
  | TILDE
  | ATSIGN
  | RECORD_FUN
  | DOT
  | COMMA
  | WILDCARD
  | BTICK
  | EOF

let show (t : token) : string =
  let open Printf in
  match t with
  | INT i -> sprintf "INT %d" i
  | TY_INT -> sprintf "TY_INT"
  | FLOAT f -> sprintf "FLOAT %.5f" f
  | TY_FLOAT -> sprintf "TY_FLOAT"
  | STRING s -> sprintf "STRING \"%s\"" s
  | TY_STRING -> sprintf "TY_STRING"
  | CHAR c -> sprintf "CHAR %c" c
  | TY_CHAR -> sprintf "TY_CHAR"
  | BOOL b -> sprintf "BOOL %b" b
  | TY_BOOL -> sprintf "TY_BOOL"
  | UNIT -> "UNIT"
  | TY_UNIT -> "TY_UNIT"
  | TY_ATOM -> "TY_ATOM"
  | IDENT i -> sprintf "IDENT %s" i
  | UPPER_IDENT i -> sprintf "UPPER_IDENT %s" i
  | DOT_SEP_IDENT (i, is) ->
    sprintf "DOT_SEP_IDENT %s.%s" i (String.concat "." is)
  | OP o -> sprintf "OP %s" o
  | IMPOSSIBLE -> "IMPOSSIBLE"
  | WHEN -> "WHEN"
  | WHERE -> "WHERE"
  | WITH -> "WITH"
  | MATCH -> "MATCH"
  | TO -> "TO"
  | WITHOUT -> "WITHOUT"
  | RASSOC -> "RASSOC"
  | LASSOC -> "LASSOC"
  | IF -> "IF"
  | THEN -> "THEN"
  | ELSE -> "ELSE"
  | DEC -> "DEC"
  | TYPE -> "TYPE"
  | DEF -> "DEF"
  | FUN -> "FUN"
  | LET -> "LET"
  | IN -> "IN"
  | END -> "END"
  | MODULE -> "MODULE"
  | IMPORT -> "IMPORT"
  | ALIAS -> "ALIAS"
  | DATA -> "DATA"
  | RECORD -> "RECORD"
  | CONSTRUCTOR -> "CONSTRUCTOR"
  | UNIVERSE -> "UNIVERSE"
  | FORALL -> "FORALL"
  | STAR -> "STAR"
  | PIPE -> "PIPE"
  | LBRACE -> "LBRACE"
  | RBRACE -> "RBRACE"
  | LPAREN -> "LPAREN"
  | RPAREN -> "RPAREN"
  | LBRACK -> "LBRACK"
  | RBRACK -> "RBRACK"
  | SEMI -> "SEMI"
  | COLON -> "COLON"
  | EQ -> "EQ"
  | ASSIGNMENT -> "ASSIGNMENT"
  | ARROW -> "ARROW"
  | F_ARROW -> "F_ARROW"
  | TILDE -> "TILDE"
  | ATSIGN -> "ATSIGN"
  | RECORD_FUN -> "RECORD_FUN"
  | DOT -> "DOT"
  | COMMA -> "COMMA"
  | WILDCARD -> "WILDCARD"
  | BTICK -> "BACKTICK"
  | EOF -> "EOF"
