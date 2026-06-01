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
  | DOT_SEP_IDENT of string list
  | OP of string
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
  | TILDE
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
  | TTYPE
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
  | ATSIGN
  | RECORD_FUN
  | DOT
  | COMMA
  | WILDCARD
  | EOF

val show : token -> string
