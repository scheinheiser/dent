type t = { filename : string; start_line : int; end_line : int; start_col : int; end_col : int }

let dummy_loc = { filename = ""; start_line = 0; end_line = 0; start_col = 0; end_col = 0 }

let pp_location out loc =
  let { filename; start_line; end_line; start_col; end_col } = loc in
  let line =
    if start_line = end_line then Printf.sprintf "%d" start_line
    else Printf.sprintf "%d-%d" start_line end_line
  in
  let col =
    if start_col = end_col then Printf.sprintf "%d" start_col
    else Printf.sprintf "%d-%d" start_col end_col
  in
  let filename = if filename = "" then "<unnamed>" else filename in
  Format.fprintf out "%s; %s:%s" filename line col


let of_lexbuf lexbuf =
  let start = Sedlexing.lexing_position_start lexbuf in
  let end_ = Sedlexing.lexing_position_curr lexbuf in
  assert (start.pos_fname = end_.pos_fname);
  {
    filename = start.pos_fname;
    start_line = start.pos_lnum;
    end_line = end_.pos_lnum;
    start_col = 1 + start.pos_cnum - start.pos_bol;
    end_col = end_.pos_cnum - end_.pos_bol;
  }


let combine l r =
  let { filename; start_line; end_line = _; start_col; end_col = _ } = l
  and { filename = _; start_line = _; end_line; start_col = _; end_col } = r in
  { filename; start_line; end_line; start_col; end_col }
