
module MenhirBasics = struct
  
  exception Error
  
  let _eRR : exn =
    Error
  
  type token = LpLexer.token
  
end

include MenhirBasics

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState277
  | MenhirState274
  | MenhirState269
  | MenhirState264
  | MenhirState262
  | MenhirState261
  | MenhirState257
  | MenhirState255
  | MenhirState254
  | MenhirState250
  | MenhirState247
  | MenhirState236
  | MenhirState234
  | MenhirState232
  | MenhirState230
  | MenhirState227
  | MenhirState223
  | MenhirState221
  | MenhirState216
  | MenhirState214
  | MenhirState212
  | MenhirState209
  | MenhirState206
  | MenhirState202
  | MenhirState200
  | MenhirState197
  | MenhirState195
  | MenhirState191
  | MenhirState188
  | MenhirState187
  | MenhirState185
  | MenhirState183
  | MenhirState177
  | MenhirState176
  | MenhirState175
  | MenhirState174
  | MenhirState173
  | MenhirState172
  | MenhirState171
  | MenhirState169
  | MenhirState160
  | MenhirState155
  | MenhirState143
  | MenhirState141
  | MenhirState137
  | MenhirState134
  | MenhirState130
  | MenhirState127
  | MenhirState115
  | MenhirState114
  | MenhirState110
  | MenhirState109
  | MenhirState107
  | MenhirState105
  | MenhirState100
  | MenhirState98
  | MenhirState95
  | MenhirState93
  | MenhirState89
  | MenhirState85
  | MenhirState76
  | MenhirState66
  | MenhirState64
  | MenhirState62
  | MenhirState60
  | MenhirState54
  | MenhirState44
  | MenhirState42
  | MenhirState41
  | MenhirState38
  | MenhirState36
  | MenhirState35
  | MenhirState32
  | MenhirState28
  | MenhirState27
  | MenhirState26
  | MenhirState25
  | MenhirState24
  | MenhirState23
  | MenhirState22
  | MenhirState21
  | MenhirState20
  | MenhirState19
  | MenhirState16
  | MenhirState14
  | MenhirState11
  | MenhirState7
  | MenhirState6
  | MenhirState3
  | MenhirState0

# 4 "src/parsing/lpParser.mly"
  
  open Lplib
  open Common
  open Pos
  open Syntax
  open Core

  let qid_of_path loc p =
    let (mp, id) = List.split_last p in make_pos loc (mp, id)

  let make_abst startpos ps t endpos =
    if ps = [] then t else make_pos (startpos,endpos) (P_Abst(ps,t))

  let make_prod startpos ps t endpos =
    if ps = [] then t else make_pos (startpos,endpos) (P_Prod(ps,t))

# 132 "src/parsing/lpParser.ml"

let rec _menhir_goto_separated_nonempty_list_WITH_inductive_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_separated_nonempty_list_WITH_inductive_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState254 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv1043 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * Lexing.position) * _menhir_state * 'tv_separated_nonempty_list_WITH_inductive_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv1039 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * Lexing.position) * _menhir_state * 'tv_separated_nonempty_list_WITH_inductive_) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv1037 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * Lexing.position) * _menhir_state * 'tv_separated_nonempty_list_WITH_inductive_) = Obj.magic _menhir_stack in
            let (_endpos__5_ : Lexing.position) = _endpos in
            ((let ((((_menhir_stack, _endpos_ms_, _menhir_s, (ms : 'tv_list_modifier_), _startpos_ms_), _endpos_xs_, _, (xs : 'tv_list_params_), _startpos_xs_), _startpos__3_), _, (is : 'tv_separated_nonempty_list_WITH_inductive_)) = _menhir_stack in
            let _v : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 155 "src/parsing/lpParser.ml"
            ) = let _endpos = _endpos__5_ in
            let _symbolstartpos = if _startpos_ms_ != _endpos_ms_ then
              _startpos_ms_
            else
              if _startpos_xs_ != _endpos_xs_ then
                _startpos_xs_
              else
                _startpos__3_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 282 "src/parsing/lpParser.mly"
      ( make_pos _sloc (P_inductive(ms,xs,is)) )
# 168 "src/parsing/lpParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1038)) : 'freshtv1040)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv1041 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * Lexing.position) * _menhir_state * 'tv_separated_nonempty_list_WITH_inductive_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1042)) : 'freshtv1044)
    | MenhirState274 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1047 * _menhir_state * 'tv_inductive)) * _menhir_state * 'tv_separated_nonempty_list_WITH_inductive_) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1045 * _menhir_state * 'tv_inductive)) * _menhir_state * 'tv_separated_nonempty_list_WITH_inductive_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (x : 'tv_inductive)), _, (xs : 'tv_separated_nonempty_list_WITH_inductive_)) = _menhir_stack in
        let _v : 'tv_separated_nonempty_list_WITH_inductive_ = 
# 243 "<standard.mly>"
    ( x :: xs )
# 187 "src/parsing/lpParser.ml"
         in
        _menhir_goto_separated_nonempty_list_WITH_inductive_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1046)) : 'freshtv1048)
    | _ ->
        _menhir_fail ()

and _menhir_goto_loption_separated_nonempty_list_VBAR_constructor__ : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_loption_separated_nonempty_list_VBAR_constructor__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ((((('freshtv1035 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) * Lexing.position * 'tv_option_VBAR_) = Obj.magic _menhir_stack in
    let (_endpos : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_loption_separated_nonempty_list_VBAR_constructor__) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ((((('freshtv1033 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) * Lexing.position * 'tv_option_VBAR_) = Obj.magic _menhir_stack in
    let (_endpos_xs_ : Lexing.position) = _endpos in
    let (_ : _menhir_state) = _menhir_s in
    let ((xs : 'tv_loption_separated_nonempty_list_VBAR_constructor__) : 'tv_loption_separated_nonempty_list_VBAR_constructor__) = _v in
    ((let (((((_menhir_stack, _endpos_i_, _menhir_s, (i : 'tv_uid), _startpos_i_), _endpos_ps_, _, (ps : 'tv_list_params_), _startpos_ps_), _endpos_t_, _, (t : 'tv_term), _startpos_t_), _endpos__5_), _endpos__6_, _) = _menhir_stack in
    let _v : 'tv_inductive = let l = 
# 232 "<standard.mly>"
    ( xs )
# 209 "src/parsing/lpParser.ml"
     in
    let _endpos_l_ = _endpos_xs_ in
    let _endpos = _endpos_l_ in
    let _symbolstartpos = _startpos_i_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 251 "src/parsing/lpParser.mly"
    ( let t = make_prod _startpos_ps_ ps t _endpos_t_ in
      make_pos _sloc (i,t,l) )
# 219 "src/parsing/lpParser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1031) = _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_inductive) = _v in
    ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1029 * _menhir_state * 'tv_inductive) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.WITH ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1023 * _menhir_state * 'tv_inductive) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState274 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState274) : 'freshtv1024)
    | LpLexer.SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1025 * _menhir_state * 'tv_inductive) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (x : 'tv_inductive)) = _menhir_stack in
        let _v : 'tv_separated_nonempty_list_WITH_inductive_ = 
# 241 "<standard.mly>"
    ( [ x ] )
# 250 "src/parsing/lpParser.ml"
         in
        _menhir_goto_separated_nonempty_list_WITH_inductive_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1026)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1027 * _menhir_state * 'tv_inductive) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1028)) : 'freshtv1030)) : 'freshtv1032)) : 'freshtv1034)) : 'freshtv1036)

and _menhir_goto_nonempty_list_params_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_nonempty_list_params_ -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState28 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1015 * Lexing.position * _menhir_state * 'tv_params * Lexing.position) * _menhir_state * 'tv_nonempty_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1013 * Lexing.position * _menhir_state * 'tv_params * Lexing.position) * _menhir_state * 'tv_nonempty_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_params), _startpos_x_), _, (xs : 'tv_nonempty_list_params_), _startpos_xs_) = _menhir_stack in
        let _startpos = _startpos_x_ in
        let _v : 'tv_nonempty_list_params_ = 
# 223 "<standard.mly>"
    ( x :: xs )
# 275 "src/parsing/lpParser.ml"
         in
        _menhir_goto_nonempty_list_params_ _menhir_env _menhir_stack _menhir_s _v _startpos) : 'freshtv1014)) : 'freshtv1016)
    | MenhirState11 | MenhirState27 | MenhirState36 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1021 * _menhir_state * 'tv_nonempty_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1017 * _menhir_state * 'tv_nonempty_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState38 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38) : 'freshtv1018)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1019 * _menhir_state * 'tv_nonempty_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1020)) : 'freshtv1022)
    | _ ->
        _menhir_fail ()

and _menhir_goto_proof_end : _menhir_env -> 'ttv_tail -> 'tv_proof_end -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv1011 * _menhir_state) * _menhir_state * 'tv_list_terminated_tactic_SEMICOLON__) = Obj.magic _menhir_stack in
    let (_v : 'tv_proof_end) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv1009 * _menhir_state) * _menhir_state * 'tv_list_terminated_tactic_SEMICOLON__) = Obj.magic _menhir_stack in
    let ((pe : 'tv_proof_end) : 'tv_proof_end) = _v in
    ((let ((_menhir_stack, _menhir_s), _, (ts : 'tv_list_terminated_tactic_SEMICOLON__)) = _menhir_stack in
    let _v : 'tv_proof = 
# 242 "src/parsing/lpParser.mly"
                                                            ( ts, pe )
# 344 "src/parsing/lpParser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1007) = _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_proof) = _v in
    ((match _menhir_s with
    | MenhirState176 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv997) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_proof) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv995) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((x : 'tv_proof) : 'tv_proof) = _v in
        ((let _v : 'tv_option_proof_ = 
# 116 "<standard.mly>"
    ( Some x )
# 363 "src/parsing/lpParser.ml"
         in
        _menhir_goto_option_proof_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv996)) : 'freshtv998)
    | MenhirState250 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1001 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_proof) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv999 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((p : 'tv_proof) : 'tv_proof) = _v in
        ((let (_menhir_stack, _endpos_t_, _menhir_s, (t : 'tv_term), _startpos_t_) = _menhir_stack in
        let _v : 'tv_term_proof = 
# 257 "src/parsing/lpParser.mly"
                   ( Some t, Some p )
# 379 "src/parsing/lpParser.ml"
         in
        _menhir_goto_term_proof _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1000)) : 'freshtv1002)
    | MenhirState247 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1005) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_proof) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1003) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((p : 'tv_proof) : 'tv_proof) = _v in
        ((let _v : 'tv_term_proof = 
# 256 "src/parsing/lpParser.mly"
            ( None, Some p )
# 394 "src/parsing/lpParser.ml"
         in
        _menhir_goto_term_proof _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1004)) : 'freshtv1006)
    | _ ->
        _menhir_fail ()) : 'freshtv1008)) : 'freshtv1010)) : 'freshtv1012)

and _menhir_goto_option_preceded_COLON_term__ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_preceded_COLON_term__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv981 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_) * _menhir_state * 'tv_option_preceded_COLON_term__) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.R_CU_BRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv977 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_) * _menhir_state * 'tv_option_preceded_COLON_term__) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv975 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_) * _menhir_state * 'tv_option_preceded_COLON_term__) = Obj.magic _menhir_stack in
            let (_endpos__4_ : Lexing.position) = _endpos in
            ((let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_xs_, _, (xs : 'tv_nonempty_list_param_id_)), _, (a : 'tv_option_preceded_COLON_term__)) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__4_ in
            let _v : 'tv_params = 
# 152 "src/parsing/lpParser.mly"
    ( (xs, a, true) )
# 424 "src/parsing/lpParser.ml"
             in
            _menhir_goto_params _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv976)) : 'freshtv978)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv979 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_) * _menhir_state * 'tv_option_preceded_COLON_term__) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv980)) : 'freshtv982)
    | MenhirState62 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv987 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.ASSIGN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv983 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState64) : 'freshtv984)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv985 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv986)) : 'freshtv988)
    | MenhirState174 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv993 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.ASSIGN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv989 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.BEGIN ->
                _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState247
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState247 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState247 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState247 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState247 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState247 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState247 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState247 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState247 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState247) : 'freshtv990)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv991 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv992)) : 'freshtv994)
    | _ ->
        _menhir_fail ()

and _menhir_goto_separated_nonempty_list_VBAR_constructor_ : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_separated_nonempty_list_VBAR_constructor_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    match _menhir_s with
    | MenhirState261 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv969) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_VBAR_constructor_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv967) = Obj.magic _menhir_stack in
        let (_endpos_x_ : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((x : 'tv_separated_nonempty_list_VBAR_constructor_) : 'tv_separated_nonempty_list_VBAR_constructor_) = _v in
        ((let _endpos = _endpos_x_ in
        let _v : 'tv_loption_separated_nonempty_list_VBAR_constructor__ = 
# 144 "<standard.mly>"
    ( x )
# 563 "src/parsing/lpParser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_VBAR_constructor__ _menhir_env _menhir_stack _endpos _menhir_s _v) : 'freshtv968)) : 'freshtv970)
    | MenhirState269 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv973 * Lexing.position * _menhir_state * 'tv_constructor) * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_VBAR_constructor_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv971 * Lexing.position * _menhir_state * 'tv_constructor) * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_xs_ : Lexing.position) = _endpos in
        let (_ : _menhir_state) = _menhir_s in
        let ((xs : 'tv_separated_nonempty_list_VBAR_constructor_) : 'tv_separated_nonempty_list_VBAR_constructor_) = _v in
        ((let ((_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_constructor)), _endpos__2_) = _menhir_stack in
        let _endpos = _endpos_xs_ in
        let _v : 'tv_separated_nonempty_list_VBAR_constructor_ = 
# 243 "<standard.mly>"
    ( x :: xs )
# 582 "src/parsing/lpParser.ml"
         in
        _menhir_goto_separated_nonempty_list_VBAR_constructor_ _menhir_env _menhir_stack _endpos _menhir_s _v) : 'freshtv972)) : 'freshtv974)
    | _ ->
        _menhir_fail ()

and _menhir_goto_option_VBAR_ : _menhir_env -> 'ttv_tail -> Lexing.position -> 'tv_option_VBAR_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _v ->
    let _menhir_stack = (_menhir_stack, _endpos, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ((((('freshtv965 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) * Lexing.position * 'tv_option_VBAR_) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.UID _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState261 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.SEMICOLON | LpLexer.WITH ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv963) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState261 in
        ((let (_, _endpos) = Obj.magic _menhir_stack in
        let _v : 'tv_loption_separated_nonempty_list_VBAR_constructor__ = 
# 142 "<standard.mly>"
    ( [] )
# 606 "src/parsing/lpParser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_VBAR_constructor__ _menhir_env _menhir_stack _endpos _menhir_s _v) : 'freshtv964)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState261) : 'freshtv966)

and _menhir_goto_term_proof : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_term_proof -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (((((('freshtv961 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) * Lexing.position) * _menhir_state * 'tv_term_proof) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv957 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) * Lexing.position) * _menhir_state * 'tv_term_proof) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv955 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) * Lexing.position) * _menhir_state * 'tv_term_proof) = Obj.magic _menhir_stack in
        let (_endpos__8_ : Lexing.position) = _endpos in
        ((let (((((((_menhir_stack, _endpos_ms_, _menhir_s, (ms : 'tv_list_modifier_), _startpos_ms_), _, _startpos__2_), _endpos_s_, _, (s : 'tv_uid), _startpos_s_), _endpos_al_, _, (al : 'tv_list_params_), _startpos_al_), _, (ao : 'tv_option_preceded_COLON_term__)), _endpos__6_), _, (tp : 'tv_term_proof)) = _menhir_stack in
        let _v : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 633 "src/parsing/lpParser.ml"
        ) = let _endpos = _endpos__8_ in
        let _symbolstartpos = if _startpos_ms_ != _endpos_ms_ then
          _startpos_ms_
        else
          _startpos__2_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 276 "src/parsing/lpParser.mly"
    ( let sym =
        {p_sym_mod=ms; p_sym_nam=s; p_sym_arg=al; p_sym_typ=ao;
         p_sym_trm=fst tp; p_sym_prf=snd tp; p_sym_def=true}
      in make_pos _sloc (P_symbol(sym)) )
# 646 "src/parsing/lpParser.ml"
         in
        _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv956)) : 'freshtv958)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv959 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) * Lexing.position) * _menhir_state * 'tv_term_proof) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv960)) : 'freshtv962)

and _menhir_goto_option_preceded_IN_term__ : _menhir_env -> 'ttv_tail -> Lexing.position -> 'tv_option_preceded_IN_term__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv953 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
    let (_endpos : Lexing.position) = _endpos in
    let (_v : 'tv_option_preceded_IN_term__) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv951 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
    let (_endpos_t_ : Lexing.position) = _endpos in
    let ((t : 'tv_option_preceded_IN_term__) : 'tv_option_preceded_IN_term__) = _v in
    ((let (((_menhir_stack, _endpos_u_, _menhir_s, (u : 'tv_term), _startpos_u_), _startpos__2_), _endpos_x_, _, (x : 'tv_term), _startpos_x_) = _menhir_stack in
    match try
      Some ((let _endpos = _endpos_t_ in
      let _symbolstartpos = _startpos_u_ in
      let _sloc = (_symbolstartpos, _endpos) in
      
# 159 "src/parsing/lpParser.mly"
    ( let ident_of_term {elt; _} =
        match elt with
        | P_Iden({elt=([], x); pos}, _) -> Pos.make pos x
        | _ -> (raise _eRR)
      in
      match t with
      | Some(t) -> make_pos _sloc (Rw_TermInIdInTerm(u, (ident_of_term x, t)))
      | None -> make_pos _sloc (Rw_IdInTerm(ident_of_term u, x))
    )
# 683 "src/parsing/lpParser.ml"
      ) : 'tv_rw_patt)
    with
    | Error ->
        None with
    | Some _v ->
        _menhir_goto_rw_patt _menhir_env _menhir_stack _menhir_s _v
    | None ->
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv952)) : 'freshtv954)

and _menhir_goto_rw_patt : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_rw_patt -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv949) * _menhir_state * 'tv_rw_patt) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.R_SQ_BRACKET ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv945) * _menhir_state * 'tv_rw_patt) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv943) * _menhir_state * 'tv_rw_patt) = Obj.magic _menhir_stack in
        let (_endpos__3_ : Lexing.position) = _endpos in
        ((let (_menhir_stack, _, (x : 'tv_rw_patt)) = _menhir_stack in
        let _v : 'tv_option_delimited_L_SQ_BRACKET_rw_patt_R_SQ_BRACKET__ = let x = 
# 200 "<standard.mly>"
    ( x )
# 714 "src/parsing/lpParser.ml"
         in
        
# 116 "<standard.mly>"
    ( Some x )
# 719 "src/parsing/lpParser.ml"
         in
        _menhir_goto_option_delimited_L_SQ_BRACKET_rw_patt_R_SQ_BRACKET__ _menhir_env _menhir_stack _v) : 'freshtv944)) : 'freshtv946)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv947) * _menhir_state * 'tv_rw_patt) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv948)) : 'freshtv950)

and _menhir_goto_option_proof_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_proof_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (((((('freshtv941 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * _menhir_state * 'tv_option_proof_) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv937 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * _menhir_state * 'tv_option_proof_) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv935 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * _menhir_state * 'tv_option_proof_) = Obj.magic _menhir_stack in
        let (_endpos__8_ : Lexing.position) = _endpos in
        ((let (((((((_menhir_stack, _endpos_ms_, _menhir_s, (ms : 'tv_list_modifier_), _startpos_ms_), _, _startpos__2_), _endpos_s_, _, (s : 'tv_uid), _startpos_s_), _endpos_al_, _, (al : 'tv_list_params_), _startpos_al_), _), _endpos_a_, _, (a : 'tv_term), _startpos_a_), _, (po : 'tv_option_proof_)) = _menhir_stack in
        let _v : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 749 "src/parsing/lpParser.ml"
        ) = let _endpos = _endpos__8_ in
        let _symbolstartpos = if _startpos_ms_ != _endpos_ms_ then
          _startpos_ms_
        else
          _startpos__2_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 270 "src/parsing/lpParser.mly"
    ( let sym =
        {p_sym_mod=ms; p_sym_nam=s; p_sym_arg=al; p_sym_typ=Some(a);
         p_sym_trm=None; p_sym_def=false; p_sym_prf=po}
      in make_pos _sloc (P_symbol(sym)) )
# 762 "src/parsing/lpParser.ml"
         in
        _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv936)) : 'freshtv938)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv939 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * _menhir_state * 'tv_option_proof_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv940)) : 'freshtv942)

and _menhir_run177 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.ADMIT ->
        _menhir_run225 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.APPLY ->
        _menhir_run223 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ASSERT ->
        _menhir_run164 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ASSERTNOT ->
        _menhir_run163 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ASSUME ->
        _menhir_run221 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.COMPUTE ->
        _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.DEBUG ->
        _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.FAIL ->
        _menhir_run220 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.FLAG ->
        _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.FOCUS ->
        _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.GENERALIZE ->
        _menhir_run216 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.HAVE ->
        _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.INDUCTION ->
        _menhir_run211 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PRINT ->
        _menhir_run127 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PROOFTERM ->
        _menhir_run125 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PROVER ->
        _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PROVER_TIMEOUT ->
        _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.REFINE ->
        _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.REFLEXIVITY ->
        _menhir_run208 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.REWRITE ->
        _menhir_run185 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.SIMPLIFY ->
        _menhir_run183 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.SOLVE ->
        _menhir_run182 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.SYMMETRY ->
        _menhir_run181 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.TYPE_QUERY ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.VERBOSE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WHY3 ->
        _menhir_run178 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState177 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ABORT | LpLexer.ADMITTED | LpLexer.END ->
        _menhir_reduce45 _menhir_env (Obj.magic _menhir_stack) MenhirState177
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState177

and _menhir_goto_separated_nonempty_list_WITH_rule_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_separated_nonempty_list_WITH_rule_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState98 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv929 * _menhir_state * Lexing.position) * _menhir_state * 'tv_separated_nonempty_list_WITH_rule_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv925 * _menhir_state * Lexing.position) * _menhir_state * 'tv_separated_nonempty_list_WITH_rule_) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv923 * _menhir_state * Lexing.position) * _menhir_state * 'tv_separated_nonempty_list_WITH_rule_) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _, (rs : 'tv_separated_nonempty_list_WITH_rule_)) = _menhir_stack in
            let _v : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 859 "src/parsing/lpParser.ml"
            ) = let _endpos = _endpos__3_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 284 "src/parsing/lpParser.mly"
      ( make_pos _sloc (P_rules(rs)) )
# 866 "src/parsing/lpParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv924)) : 'freshtv926)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv927 * _menhir_state * Lexing.position) * _menhir_state * 'tv_separated_nonempty_list_WITH_rule_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv928)) : 'freshtv930)
    | MenhirState105 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv933 * _menhir_state * 'tv_rule)) * _menhir_state * 'tv_separated_nonempty_list_WITH_rule_) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv931 * _menhir_state * 'tv_rule)) * _menhir_state * 'tv_separated_nonempty_list_WITH_rule_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (x : 'tv_rule)), _, (xs : 'tv_separated_nonempty_list_WITH_rule_)) = _menhir_stack in
        let _v : 'tv_separated_nonempty_list_WITH_rule_ = 
# 243 "<standard.mly>"
    ( x :: xs )
# 885 "src/parsing/lpParser.ml"
         in
        _menhir_goto_separated_nonempty_list_WITH_rule_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv932)) : 'freshtv934)
    | _ ->
        _menhir_fail ()

and _menhir_goto_separated_nonempty_list_SEMICOLON_equation_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_separated_nonempty_list_SEMICOLON_equation_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState89 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv917 * _menhir_state * 'tv_equation * Lexing.position))) * _menhir_state * 'tv_separated_nonempty_list_SEMICOLON_equation_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.R_SQ_BRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv913 * _menhir_state * 'tv_equation * Lexing.position))) * _menhir_state * 'tv_separated_nonempty_list_SEMICOLON_equation_) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv911 * _menhir_state * 'tv_equation * Lexing.position))) * _menhir_state * 'tv_separated_nonempty_list_SEMICOLON_equation_) = Obj.magic _menhir_stack in
            let (_endpos__5_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, (e : 'tv_equation), _startpos_e_), _, (es : 'tv_separated_nonempty_list_SEMICOLON_equation_)) = _menhir_stack in
            let _v : 'tv_unif_rule = let _endpos = _endpos__5_ in
            let _symbolstartpos = _startpos_e_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 335 "src/parsing/lpParser.mly"
    ( (* FIXME: give sensible positions instead of Pos.none and P.appl. *)
      let equiv = P.qiden Unif_rule.path Unif_rule.equiv.sym_name in
      let cons = P.qiden Unif_rule.path Unif_rule.cons.sym_name in
      let mk_equiv (t, u) = P.appl (P.appl equiv t) u in
      let lhs = mk_equiv e in
      let es = List.rev_map mk_equiv es in
      let (en, es) = List.(hd es, tl es) in
      let cat e es = P.appl (P.appl cons e) es in
      let rhs = List.fold_right cat es en in
      make_pos _sloc (lhs, rhs) )
# 925 "src/parsing/lpParser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv909) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_unif_rule) = _v in
            ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv907 * _menhir_state * Lexing.position) * _menhir_state * 'tv_unif_rule) = Obj.magic _menhir_stack in
            ((assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.SEMICOLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv903 * _menhir_state * Lexing.position) * _menhir_state * 'tv_unif_rule) = Obj.magic _menhir_stack in
                let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                ((let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv901 * _menhir_state * Lexing.position) * _menhir_state * 'tv_unif_rule) = Obj.magic _menhir_stack in
                let (_endpos__3_ : Lexing.position) = _endpos in
                ((let ((_menhir_stack, _menhir_s, _startpos__1_), _, (r : 'tv_unif_rule)) = _menhir_stack in
                let _v : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 948 "src/parsing/lpParser.ml"
                ) = let _endpos = _endpos__3_ in
                let _startpos = _startpos__1_ in
                let _loc = (_startpos, _endpos) in
                
# 287 "src/parsing/lpParser.mly"
                                    ( make_pos _loc (P_unif_rule(r)) )
# 955 "src/parsing/lpParser.ml"
                 in
                _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv902)) : 'freshtv904)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv905 * _menhir_state * Lexing.position) * _menhir_state * 'tv_unif_rule) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv906)) : 'freshtv908)) : 'freshtv910)) : 'freshtv912)) : 'freshtv914)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv915 * _menhir_state * 'tv_equation * Lexing.position))) * _menhir_state * 'tv_separated_nonempty_list_SEMICOLON_equation_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv916)) : 'freshtv918)
    | MenhirState93 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv921 * _menhir_state * 'tv_equation * Lexing.position) * Lexing.position) * _menhir_state * 'tv_separated_nonempty_list_SEMICOLON_equation_) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv919 * _menhir_state * 'tv_equation * Lexing.position) * Lexing.position) * _menhir_state * 'tv_separated_nonempty_list_SEMICOLON_equation_) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s, (x : 'tv_equation), _startpos_x_), _endpos__2_), _, (xs : 'tv_separated_nonempty_list_SEMICOLON_equation_)) = _menhir_stack in
        let _v : 'tv_separated_nonempty_list_SEMICOLON_equation_ = 
# 243 "<standard.mly>"
    ( x :: xs )
# 981 "src/parsing/lpParser.ml"
         in
        _menhir_goto_separated_nonempty_list_SEMICOLON_equation_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv920)) : 'freshtv922)
    | _ ->
        _menhir_fail ()

and _menhir_goto_separated_nonempty_list_SEMICOLON_term_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_separated_nonempty_list_SEMICOLON_term_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState76 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv895 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_SEMICOLON_term_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv893 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((xs : 'tv_separated_nonempty_list_SEMICOLON_term_) : 'tv_separated_nonempty_list_SEMICOLON_term_) = _v in
        ((let ((_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_term), _startpos_x_), _endpos__2_) = _menhir_stack in
        let _v : 'tv_separated_nonempty_list_SEMICOLON_term_ = 
# 243 "<standard.mly>"
    ( x :: xs )
# 1003 "src/parsing/lpParser.ml"
         in
        _menhir_goto_separated_nonempty_list_SEMICOLON_term_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv894)) : 'freshtv896)
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv899) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_separated_nonempty_list_SEMICOLON_term_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv897) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((x : 'tv_separated_nonempty_list_SEMICOLON_term_) : 'tv_separated_nonempty_list_SEMICOLON_term_) = _v in
        ((let _v : 'tv_loption_separated_nonempty_list_SEMICOLON_term__ = 
# 144 "<standard.mly>"
    ( x )
# 1018 "src/parsing/lpParser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_SEMICOLON_term__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv898)) : 'freshtv900)
    | _ ->
        _menhir_fail ()

and _menhir_goto_params : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_params -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState11 | MenhirState36 | MenhirState28 | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv889 * Lexing.position * _menhir_state * 'tv_params * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.L_CU_BRACKET ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState28 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.L_PAREN ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState28 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState28 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.WILD ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState28 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv887 * Lexing.position * _menhir_state * 'tv_params * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_params), _startpos_x_) = _menhir_stack in
            let _startpos = _startpos_x_ in
            let _v : 'tv_nonempty_list_params_ = 
# 221 "<standard.mly>"
    ( [ x ] )
# 1050 "src/parsing/lpParser.ml"
             in
            _menhir_goto_nonempty_list_params_ _menhir_env _menhir_stack _menhir_s _v _startpos) : 'freshtv888)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState28) : 'freshtv890)
    | MenhirState262 | MenhirState255 | MenhirState171 | MenhirState230 | MenhirState173 | MenhirState60 | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv891 * Lexing.position * _menhir_state * 'tv_params * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.L_CU_BRACKET ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.L_PAREN ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState60 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.WILD ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState60 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.ASSIGN | LpLexer.COLON | LpLexer.INDUCTIVE | LpLexer.TURNSTILE ->
            _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState60
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState60) : 'freshtv892)
    | _ ->
        _menhir_fail ()

and _menhir_goto_bterm : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_bterm -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    match _menhir_s with
    | MenhirState257 | MenhirState264 | MenhirState247 | MenhirState175 | MenhirState232 | MenhirState236 | MenhirState234 | MenhirState223 | MenhirState214 | MenhirState209 | MenhirState206 | MenhirState187 | MenhirState202 | MenhirState195 | MenhirState197 | MenhirState188 | MenhirState191 | MenhirState155 | MenhirState98 | MenhirState105 | MenhirState100 | MenhirState95 | MenhirState3 | MenhirState89 | MenhirState93 | MenhirState85 | MenhirState7 | MenhirState76 | MenhirState19 | MenhirState20 | MenhirState21 | MenhirState64 | MenhirState66 | MenhirState26 | MenhirState32 | MenhirState54 | MenhirState38 | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv881) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_bterm) = _v in
        let (_startpos : Lexing.position) = _startpos in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv879) = Obj.magic _menhir_stack in
        let (_endpos_t_ : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((t : 'tv_bterm) : 'tv_bterm) = _v in
        let (_startpos_t_ : Lexing.position) = _startpos in
        ((let _startpos = _startpos_t_ in
        let _endpos = _endpos_t_ in
        let _v : 'tv_term = 
# 320 "src/parsing/lpParser.mly"
            ( t )
# 1101 "src/parsing/lpParser.ml"
         in
        _menhir_goto_term _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv880)) : 'freshtv882)
    | MenhirState41 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv885 * Lexing.position * _menhir_state * 'tv_saterm * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_bterm) = _v in
        let (_startpos : Lexing.position) = _startpos in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv883 * Lexing.position * _menhir_state * 'tv_saterm * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_u_ : Lexing.position) = _endpos in
        let (_ : _menhir_state) = _menhir_s in
        let ((u : 'tv_bterm) : 'tv_bterm) = _v in
        let (_startpos_u_ : Lexing.position) = _startpos in
        ((let (_menhir_stack, _endpos_t_, _menhir_s, (t : 'tv_saterm), _startpos_t_) = _menhir_stack in
        let _startpos = _startpos_t_ in
        let _endpos = _endpos_u_ in
        let _v : 'tv_term = let _endpos = _endpos_u_ in
        let _symbolstartpos = _startpos_t_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 322 "src/parsing/lpParser.mly"
                     ( make_pos _sloc (P_Appl(t,u)) )
# 1126 "src/parsing/lpParser.ml"
         in
        _menhir_goto_term _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv884)) : 'freshtv886)
    | _ ->
        _menhir_fail ()

and _menhir_reduce79 : _menhir_env -> ('ttv_tail * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let ((_menhir_stack, _menhir_s), _endpos_x_, _, (x : 'tv_term), _startpos_x_) = _menhir_stack in
    let _v : 'tv_option_preceded_COLON_term__ = let x = 
# 183 "<standard.mly>"
    ( x )
# 1138 "src/parsing/lpParser.ml"
     in
    
# 116 "<standard.mly>"
    ( Some x )
# 1143 "src/parsing/lpParser.ml"
     in
    _menhir_goto_option_preceded_COLON_term__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_binder : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_binder -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    match _menhir_s with
    | MenhirState36 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv869 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term_id * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_binder) = _v in
        let (_startpos : Lexing.position) = _startpos in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv867 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term_id * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_b_ : Lexing.position) = _endpos in
        let (_ : _menhir_state) = _menhir_s in
        let ((b : 'tv_binder) : 'tv_binder) = _v in
        let (_startpos_b_ : Lexing.position) = _startpos in
        ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_q_, _, (q : 'tv_term_id), _startpos_q_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_b_ in
        let _v : 'tv_bterm = let _endpos = _endpos_b_ in
        let _symbolstartpos = _startpos__1_ in
        let _loc_b_ = (_startpos_b_, _endpos_b_) in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 312 "src/parsing/lpParser.mly"
    ( let b = make_pos _loc_b_ (P_Abst(fst b, snd b)) in
      make_pos _sloc (P_Appl(q, b)) )
# 1174 "src/parsing/lpParser.ml"
         in
        _menhir_goto_bterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv868)) : 'freshtv870)
    | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv873 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_binder) = _v in
        let (_startpos : Lexing.position) = _startpos in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv871 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_b_ : Lexing.position) = _endpos in
        let (_ : _menhir_state) = _menhir_s in
        let ((b : 'tv_binder) : 'tv_binder) = _v in
        let (_startpos_b_ : Lexing.position) = _startpos in
        ((let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_b_ in
        let _v : 'tv_bterm = let _endpos = _endpos_b_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 315 "src/parsing/lpParser.mly"
                    ( make_pos _sloc (P_Abst(fst b, snd b)) )
# 1199 "src/parsing/lpParser.ml"
         in
        _menhir_goto_bterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv872)) : 'freshtv874)
    | MenhirState11 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv877 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_binder) = _v in
        let (_startpos : Lexing.position) = _startpos in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv875 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_b_ : Lexing.position) = _endpos in
        let (_ : _menhir_state) = _menhir_s in
        let ((b : 'tv_binder) : 'tv_binder) = _v in
        let (_startpos_b_ : Lexing.position) = _startpos in
        ((let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_b_ in
        let _v : 'tv_bterm = let _endpos = _endpos_b_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 314 "src/parsing/lpParser.mly"
                ( make_pos _sloc (P_Prod(fst b, snd b)) )
# 1224 "src/parsing/lpParser.ml"
         in
        _menhir_goto_bterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv876)) : 'freshtv878)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_terminated_tactic_SEMICOLON__ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_list_terminated_tactic_SEMICOLON__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState227 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv849 * _menhir_state * 'tv_tactic) * Lexing.position) * _menhir_state * 'tv_list_terminated_tactic_SEMICOLON__) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv847 * _menhir_state * 'tv_tactic) * Lexing.position) * _menhir_state * 'tv_list_terminated_tactic_SEMICOLON__) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s, (x : 'tv_tactic)), _endpos__2_), _, (xs : 'tv_list_terminated_tactic_SEMICOLON__)) = _menhir_stack in
        let _v : 'tv_list_terminated_tactic_SEMICOLON__ = let x = 
# 191 "<standard.mly>"
    ( x )
# 1243 "src/parsing/lpParser.ml"
         in
        
# 213 "<standard.mly>"
    ( x :: xs )
# 1248 "src/parsing/lpParser.ml"
         in
        _menhir_goto_list_terminated_tactic_SEMICOLON__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv848)) : 'freshtv850)
    | MenhirState177 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv865 * _menhir_state) * _menhir_state * 'tv_list_terminated_tactic_SEMICOLON__) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.ABORT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv853) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv851) = Obj.magic _menhir_stack in
            let (_endpos__1_ : Lexing.position) = _endpos in
            let (_startpos__1_ : Lexing.position) = _startpos in
            ((let _v : 'tv_proof_end = let _endpos = _endpos__1_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 238 "src/parsing/lpParser.mly"
          ( make_pos _sloc Syntax.P_proof_abort )
# 1273 "src/parsing/lpParser.ml"
             in
            _menhir_goto_proof_end _menhir_env _menhir_stack _v) : 'freshtv852)) : 'freshtv854)
        | LpLexer.ADMITTED ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv857) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv855) = Obj.magic _menhir_stack in
            let (_endpos__1_ : Lexing.position) = _endpos in
            let (_startpos__1_ : Lexing.position) = _startpos in
            ((let _v : 'tv_proof_end = let _endpos = _endpos__1_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 239 "src/parsing/lpParser.mly"
             ( make_pos _sloc Syntax.P_proof_admitted )
# 1292 "src/parsing/lpParser.ml"
             in
            _menhir_goto_proof_end _menhir_env _menhir_stack _v) : 'freshtv856)) : 'freshtv858)
        | LpLexer.END ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv861) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv859) = Obj.magic _menhir_stack in
            let (_endpos__1_ : Lexing.position) = _endpos in
            let (_startpos__1_ : Lexing.position) = _startpos in
            ((let _v : 'tv_proof_end = let _endpos = _endpos__1_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 240 "src/parsing/lpParser.mly"
        ( make_pos _sloc Syntax.P_proof_end )
# 1311 "src/parsing/lpParser.ml"
             in
            _menhir_goto_proof_end _menhir_env _menhir_stack _v) : 'freshtv860)) : 'freshtv862)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv863 * _menhir_state) * _menhir_state * 'tv_list_terminated_tactic_SEMICOLON__) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv864)) : 'freshtv866)
    | _ ->
        _menhir_fail ()

and _menhir_goto_option_STRINGLIT_ : _menhir_env -> 'ttv_tail -> Lexing.position -> 'tv_option_STRINGLIT_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv845 * Lexing.position * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
    let (_endpos : Lexing.position) = _endpos in
    let (_v : 'tv_option_STRINGLIT_) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv843 * Lexing.position * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
    let (_endpos_s_ : Lexing.position) = _endpos in
    let ((s : 'tv_option_STRINGLIT_) : 'tv_option_STRINGLIT_) = _v in
    ((let (_menhir_stack, _endpos__1_, _menhir_s, _startpos__1_) = _menhir_stack in
    let _v : 'tv_tactic = let _endpos = _endpos_s_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 188 "src/parsing/lpParser.mly"
                      ( make_pos _sloc (P_tac_why3 s) )
# 1341 "src/parsing/lpParser.ml"
     in
    _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv844)) : 'freshtv846)

and _menhir_reduce78 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_option_preceded_COLON_term__ = 
# 114 "<standard.mly>"
    ( None )
# 1350 "src/parsing/lpParser.ml"
     in
    _menhir_goto_option_preceded_COLON_term__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run26 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.BACKQUOTE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState26 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ID_EXPL _v ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState26 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.INT _v ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState26 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LAMBDA ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState26 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LET ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState26 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_CU_BRACKET ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState26 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_PAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState26 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PI ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState26 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.QID _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState26 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.TYPE_TERM ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState26 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState26 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_META _v ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState26 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_PAT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState26 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState26 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState26

and _menhir_reduce86 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_param_id), _startpos_x_) = _menhir_stack in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : 'tv_params = 
# 149 "src/parsing/lpParser.mly"
               ( ([x], None, false) )
# 1401 "src/parsing/lpParser.ml"
     in
    _menhir_goto_params _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_goto_nonempty_list_param_id_ : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_nonempty_list_param_id_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv829 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv827 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_param_id), _startpos_x_), _endpos_xs_, _, (xs : 'tv_nonempty_list_param_id_)) = _menhir_stack in
        let _endpos = _endpos_xs_ in
        let _v : 'tv_nonempty_list_param_id_ = 
# 223 "<standard.mly>"
    ( x :: xs )
# 1419 "src/parsing/lpParser.ml"
         in
        _menhir_goto_nonempty_list_param_id_ _menhir_env _menhir_stack _endpos _menhir_s _v) : 'freshtv828)) : 'freshtv830)
    | MenhirState14 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv835 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv831 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState19 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState19 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState19 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState19 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState19 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState19 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState19 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState19 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState19) : 'freshtv832)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv833 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv834)) : 'freshtv836)
    | MenhirState24 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv837 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.COLON ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState25
        | LpLexer.R_CU_BRACKET ->
            _menhir_reduce78 _menhir_env (Obj.magic _menhir_stack) MenhirState25
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25) : 'freshtv838)
    | MenhirState221 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv841 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv839 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_xs_, _, (xs : 'tv_nonempty_list_param_id_)) = _menhir_stack in
        let _v : 'tv_tactic = let _endpos = _endpos_xs_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 174 "src/parsing/lpParser.mly"
                        ( make_pos _sloc (P_tac_assume xs) )
# 1499 "src/parsing/lpParser.ml"
         in
        _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv840)) : 'freshtv842)
    | _ ->
        _menhir_fail ()

and _menhir_goto_term : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_term -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv607 * _menhir_state * 'tv_nonempty_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv605 * _menhir_state * 'tv_nonempty_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ps : 'tv_nonempty_list_params_), _startpos_ps_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
        let _startpos = _startpos_ps_ in
        let _endpos = _endpos_t_ in
        let _v : 'tv_binder = 
# 326 "src/parsing/lpParser.mly"
                            ( (ps, t) )
# 1520 "src/parsing/lpParser.ml"
         in
        _menhir_goto_binder _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv606)) : 'freshtv608)
    | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv611 * Lexing.position * _menhir_state * 'tv_saterm * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv609 * Lexing.position * _menhir_state * 'tv_saterm * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _endpos_t_, _menhir_s, (t : 'tv_saterm), _startpos_t_), _), _endpos_u_, _, (u : 'tv_term), _startpos_u_) = _menhir_stack in
        let _startpos = _startpos_t_ in
        let _endpos = _endpos_u_ in
        let _v : 'tv_term = let _endpos = _endpos_u_ in
        let _symbolstartpos = _startpos_t_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 323 "src/parsing/lpParser.mly"
                          ( make_pos _sloc (P_Arro(t, u)) )
# 1537 "src/parsing/lpParser.ml"
         in
        _menhir_goto_term _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv610)) : 'freshtv612)
    | MenhirState32 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv617 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv613 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState54 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState54 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState54 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState54 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState54 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState54 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState54 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState54 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState54) : 'freshtv614)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv615 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv616)) : 'freshtv618)
    | MenhirState54 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv621 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv619 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _endpos_p_, _menhir_s, (p : 'tv_param_id), _startpos_p_), _endpos_a_, _, (a : 'tv_term), _startpos_a_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
        let _startpos = _startpos_p_ in
        let _endpos = _endpos_t_ in
        let _v : 'tv_binder = 
# 327 "src/parsing/lpParser.mly"
                                         ( ([[p], Some a, false], t) )
# 1602 "src/parsing/lpParser.ml"
         in
        _menhir_goto_binder _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv620)) : 'freshtv622)
    | MenhirState26 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv623 * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        (_menhir_reduce79 _menhir_env (Obj.magic _menhir_stack) : 'freshtv624)
    | MenhirState64 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv629 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.IN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv625 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState66 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState66 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState66 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState66 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState66 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState66 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState66 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState66 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState66) : 'freshtv626)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv627 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv628)) : 'freshtv630)
    | MenhirState66 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((((('freshtv633 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((((('freshtv631 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((((((((_menhir_stack, _menhir_s, _startpos__1_), _endpos_x_, _, (x : 'tv_uid), _startpos_x_), _endpos_a_, _, (a : 'tv_list_params_), _startpos_a_), _, (b : 'tv_option_preceded_COLON_term__)), _endpos__5_), _endpos_t_, _, (t : 'tv_term), _startpos_t_), _startpos__7_), _endpos_u_, _, (u : 'tv_term), _startpos_u_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_u_ in
        let _v : 'tv_bterm = let _endpos = _endpos_u_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 317 "src/parsing/lpParser.mly"
      ( make_pos _sloc (P_LLet(x, a, b, t, u)) )
# 1676 "src/parsing/lpParser.ml"
         in
        _menhir_goto_bterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv632)) : 'freshtv634)
    | MenhirState21 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv641 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.R_CU_BRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv637 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv635 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_aterm = let _endpos = _endpos__3_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 303 "src/parsing/lpParser.mly"
                                     ( make_pos _sloc (P_Expl(t)) )
# 1702 "src/parsing/lpParser.ml"
             in
            _menhir_goto_aterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv636)) : 'freshtv638)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv639 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv640)) : 'freshtv642)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv649 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.R_PAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv645 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv643 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : 'tv_aterm = let _endpos = _endpos__3_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 302 "src/parsing/lpParser.mly"
                           ( make_pos _sloc (P_Wrap(t)) )
# 1735 "src/parsing/lpParser.ml"
             in
            _menhir_goto_aterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv644)) : 'freshtv646)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv647 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv648)) : 'freshtv650)
    | MenhirState19 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv657 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.R_PAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv653 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv651 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__5_ : Lexing.position) = _endpos in
            ((let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_xs_, _, (xs : 'tv_nonempty_list_param_id_)), _endpos_a_, _, (a : 'tv_term), _startpos_a_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__5_ in
            let _v : 'tv_params = 
# 150 "src/parsing/lpParser.mly"
                                              ( (xs, Some(a), false) )
# 1765 "src/parsing/lpParser.ml"
             in
            _menhir_goto_params _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv652)) : 'freshtv654)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv655 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv656)) : 'freshtv658)
    | MenhirState76 | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv665 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv659 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState76 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState76 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState76 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState76 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState76 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState76 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState76 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState76 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState76) : 'freshtv660)
        | LpLexer.R_SQ_BRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv661 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_term), _startpos_x_) = _menhir_stack in
            let _v : 'tv_separated_nonempty_list_SEMICOLON_term_ = 
# 241 "<standard.mly>"
    ( [ x ] )
# 1828 "src/parsing/lpParser.ml"
             in
            _menhir_goto_separated_nonempty_list_SEMICOLON_term_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv662)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv663 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv664)) : 'freshtv666)
    | MenhirState93 | MenhirState89 | MenhirState3 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv671 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.EQUIV ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv667 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState85 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState85) : 'freshtv668)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv669 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv670)) : 'freshtv672)
    | MenhirState85 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv695 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv693 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_l_, _menhir_s, (l : 'tv_term), _startpos_l_), _endpos_r_, _, (r : 'tv_term), _startpos_r_) = _menhir_stack in
        let _startpos = _startpos_l_ in
        let _v : 'tv_equation = 
# 331 "src/parsing/lpParser.mly"
                              ( (l, r) )
# 1899 "src/parsing/lpParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv691) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_equation) = _v in
        let (_startpos : Lexing.position) = _startpos in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
        match _menhir_s with
        | MenhirState3 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv681 * _menhir_state * 'tv_equation * Lexing.position) = Obj.magic _menhir_stack in
            ((assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.HOOK_ARROW ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv677 * _menhir_state * 'tv_equation * Lexing.position) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | LpLexer.L_SQ_BRACKET ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ('freshtv673 * _menhir_state * 'tv_equation * Lexing.position)) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | LpLexer.BACKQUOTE ->
                        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LpLexer.ID_EXPL _v ->
                        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LpLexer.INT _v ->
                        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LpLexer.LAMBDA ->
                        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LpLexer.LET ->
                        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LpLexer.L_CU_BRACKET ->
                        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LpLexer.L_PAREN ->
                        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LpLexer.PI ->
                        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LpLexer.QID _v ->
                        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LpLexer.TYPE_TERM ->
                        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LpLexer.UID _v ->
                        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LpLexer.UID_META _v ->
                        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LpLexer.UID_PAT _v ->
                        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | LpLexer.WILD ->
                        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState89 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState89) : 'freshtv674)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ('freshtv675 * _menhir_state * 'tv_equation * Lexing.position)) = Obj.magic _menhir_stack in
                    ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv676)) : 'freshtv678)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv679 * _menhir_state * 'tv_equation * Lexing.position) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv680)) : 'freshtv682)
        | MenhirState93 | MenhirState89 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv689 * _menhir_state * 'tv_equation * Lexing.position) = Obj.magic _menhir_stack in
            ((assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.SEMICOLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv683 * _menhir_state * 'tv_equation * Lexing.position) = Obj.magic _menhir_stack in
                let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                ((let _menhir_stack = (_menhir_stack, _endpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | LpLexer.BACKQUOTE ->
                    _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.ID_EXPL _v ->
                    _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.INT _v ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.LAMBDA ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.LET ->
                    _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.L_CU_BRACKET ->
                    _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.L_PAREN ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.PI ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.QID _v ->
                    _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.TYPE_TERM ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.UID _v ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.UID_META _v ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.UID_PAT _v ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.WILD ->
                    _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState93) : 'freshtv684)
            | LpLexer.R_SQ_BRACKET ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv685 * _menhir_state * 'tv_equation * Lexing.position) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, (x : 'tv_equation), _startpos_x_) = _menhir_stack in
                let _v : 'tv_separated_nonempty_list_SEMICOLON_equation_ = 
# 241 "<standard.mly>"
    ( [ x ] )
# 2025 "src/parsing/lpParser.ml"
                 in
                _menhir_goto_separated_nonempty_list_SEMICOLON_equation_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv686)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv687 * _menhir_state * 'tv_equation * Lexing.position) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv688)) : 'freshtv690)
        | _ ->
            _menhir_fail ()) : 'freshtv692)) : 'freshtv694)) : 'freshtv696)
    | MenhirState95 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv699 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv697 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_t_ in
        let _v : 'tv_query = let _endpos = _endpos_t_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 235 "src/parsing/lpParser.mly"
    ( make_pos _sloc (P_query_infer(t, {strategy=NONE; steps=None})))
# 2051 "src/parsing/lpParser.ml"
         in
        _menhir_goto_query _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv698)) : 'freshtv700)
    | MenhirState105 | MenhirState98 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv705 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.HOOK_ARROW ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv701 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState100 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState100 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState100 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState100 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState100 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState100 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState100 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState100 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState100) : 'freshtv702)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv703 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv704)) : 'freshtv706)
    | MenhirState100 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv719 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv717 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_l_, _menhir_s, (l : 'tv_term), _startpos_l_), _endpos_r_, _, (r : 'tv_term), _startpos_r_) = _menhir_stack in
        let _v : 'tv_rule = let _endpos = _endpos_r_ in
        let _symbolstartpos = _startpos_l_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 329 "src/parsing/lpParser.mly"
                               ( make_pos _sloc (l, r) )
# 2117 "src/parsing/lpParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv715) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_rule) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv713 * _menhir_state * 'tv_rule) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.WITH ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv707 * _menhir_state * 'tv_rule) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState105 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState105) : 'freshtv708)
        | LpLexer.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv709 * _menhir_state * 'tv_rule) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (x : 'tv_rule)) = _menhir_stack in
            let _v : 'tv_separated_nonempty_list_WITH_rule_ = 
# 241 "<standard.mly>"
    ( [ x ] )
# 2174 "src/parsing/lpParser.ml"
             in
            _menhir_goto_separated_nonempty_list_WITH_rule_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv710)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv711 * _menhir_state * 'tv_rule) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv712)) : 'freshtv714)) : 'freshtv716)) : 'freshtv718)) : 'freshtv720)
    | MenhirState155 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv723 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv721 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_t_ in
        let _v : 'tv_query = let _endpos = _endpos_t_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 225 "src/parsing/lpParser.mly"
    ( make_pos _sloc (P_query_normalize(t, {strategy=SNF; steps=None})) )
# 2198 "src/parsing/lpParser.ml"
         in
        _menhir_goto_query _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv722)) : 'freshtv724)
    | MenhirState175 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv727 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.BEGIN ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | LpLexer.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv725) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState176 in
            ((let _v : 'tv_option_proof_ = 
# 114 "<standard.mly>"
    ( None )
# 2216 "src/parsing/lpParser.ml"
             in
            _menhir_goto_option_proof_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv726)
        | LpLexer.ASSIGN ->
            _menhir_reduce79 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState176) : 'freshtv728)
    | MenhirState191 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv731 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv729 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((((_menhir_stack, _menhir_s, _startpos__1_), _endpos_x_, _, (x : 'tv_uid), _startpos_x_), _startpos__3_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
        let _v : 'tv_rw_patt = let _endpos = _endpos_t_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 157 "src/parsing/lpParser.mly"
                       ( make_pos _sloc (Rw_InIdInTerm(x, t)) )
# 2237 "src/parsing/lpParser.ml"
         in
        _menhir_goto_rw_patt _menhir_env _menhir_stack _menhir_s _v) : 'freshtv730)) : 'freshtv732)
    | MenhirState188 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv735 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv733 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
        let _v : 'tv_rw_patt = let _endpos = _endpos_t_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 156 "src/parsing/lpParser.mly"
              ( make_pos _sloc (Rw_InTerm(t)) )
# 2252 "src/parsing/lpParser.ml"
         in
        _menhir_goto_rw_patt _menhir_env _menhir_stack _menhir_s _v) : 'freshtv734)) : 'freshtv736)
    | MenhirState187 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv745 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.AS ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv737 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState200 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState200) : 'freshtv738)
        | LpLexer.IN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv739 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState195 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState195 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState195 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState195 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState195 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState195 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState195 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState195 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState195) : 'freshtv740)
        | LpLexer.R_SQ_BRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv741 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _endpos_t_, _menhir_s, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _v : 'tv_rw_patt = let _endpos = _endpos_t_ in
            let _symbolstartpos = _startpos_t_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 155 "src/parsing/lpParser.mly"
           ( make_pos _sloc (Rw_Term(t)) )
# 2323 "src/parsing/lpParser.ml"
             in
            _menhir_goto_rw_patt _menhir_env _menhir_stack _menhir_s _v) : 'freshtv742)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv743 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv744)) : 'freshtv746)
    | MenhirState195 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv753 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.IN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv747) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState197) : 'freshtv748)
        | LpLexer.R_SQ_BRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv749) = Obj.magic _menhir_stack in
            ((let (_, _endpos) = Obj.magic _menhir_stack in
            let _v : 'tv_option_preceded_IN_term__ = 
# 114 "<standard.mly>"
    ( None )
# 2386 "src/parsing/lpParser.ml"
             in
            _menhir_goto_option_preceded_IN_term__ _menhir_env _menhir_stack _endpos _v) : 'freshtv750)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv751 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv752)) : 'freshtv754)
    | MenhirState197 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv757 * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv755 * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _startpos__1_), _endpos_x_, _, (x : 'tv_term), _startpos_x_) = _menhir_stack in
        let _endpos = _endpos_x_ in
        let _v : 'tv_option_preceded_IN_term__ = let x = 
# 183 "<standard.mly>"
    ( x )
# 2406 "src/parsing/lpParser.ml"
         in
        
# 116 "<standard.mly>"
    ( Some x )
# 2411 "src/parsing/lpParser.ml"
         in
        _menhir_goto_option_preceded_IN_term__ _menhir_env _menhir_stack _endpos _v) : 'freshtv756)) : 'freshtv758)
    | MenhirState202 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv761 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv759 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((((_menhir_stack, _endpos_u_, _menhir_s, (u : 'tv_term), _startpos_u_), _endpos_x_, _, (x : 'tv_uid), _startpos_x_), _startpos__4_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
        let _v : 'tv_rw_patt = let _endpos = _endpos_t_ in
        let _symbolstartpos = _startpos_u_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 168 "src/parsing/lpParser.mly"
                              ( make_pos _sloc (Rw_TermAsIdInTerm(u,(x,t))) )
# 2426 "src/parsing/lpParser.ml"
         in
        _menhir_goto_rw_patt _menhir_env _menhir_stack _menhir_s _v) : 'freshtv760)) : 'freshtv762)
    | MenhirState206 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv765 * Lexing.position * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_option_ASSOC_ * Lexing.position) * 'tv_option_delimited_L_SQ_BRACKET_rw_patt_R_SQ_BRACKET__) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv763 * Lexing.position * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_option_ASSOC_ * Lexing.position) * 'tv_option_delimited_L_SQ_BRACKET_rw_patt_R_SQ_BRACKET__) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((((_menhir_stack, _endpos__1_, _menhir_s, _startpos__1_), _endpos_d_, _, (d : 'tv_option_ASSOC_), _startpos_d_), (p : 'tv_option_delimited_L_SQ_BRACKET_rw_patt_R_SQ_BRACKET__)), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
        let _v : 'tv_tactic = let _endpos = _endpos_t_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 183 "src/parsing/lpParser.mly"
    ( let b = match d with Some Pratter.Left -> false | _ -> true in
      make_pos _sloc (P_tac_rewrite(b,p,t)) )
# 2442 "src/parsing/lpParser.ml"
         in
        _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv764)) : 'freshtv766)
    | MenhirState209 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv769 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv767 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
        let _v : 'tv_tactic = let _endpos = _endpos_t_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 180 "src/parsing/lpParser.mly"
                  ( make_pos _sloc (P_tac_refine t) )
# 2457 "src/parsing/lpParser.ml"
         in
        _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv768)) : 'freshtv770)
    | MenhirState214 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv773 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv771 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_i_, _, (i : 'tv_uid), _startpos_i_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
        let _v : 'tv_tactic = let _endpos = _endpos_t_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 178 "src/parsing/lpParser.mly"
                            ( make_pos _sloc (P_tac_have(i,t)) )
# 2472 "src/parsing/lpParser.ml"
         in
        _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv772)) : 'freshtv774)
    | MenhirState223 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv777 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv775 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
        let _v : 'tv_tactic = let _endpos = _endpos_t_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 173 "src/parsing/lpParser.mly"
                 ( make_pos _sloc (P_tac_apply t) )
# 2487 "src/parsing/lpParser.ml"
         in
        _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv776)) : 'freshtv778)
    | MenhirState232 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv785 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv779 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState236 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState236 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState236 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState236 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState236 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState236 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState236 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState236 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState236 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState236 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState236 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState236 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState236 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState236 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState236) : 'freshtv780)
        | LpLexer.EQUIV ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv781 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState234 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState234) : 'freshtv782)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv783 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv784)) : 'freshtv786)
    | MenhirState234 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv789 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv787 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((((_menhir_stack, _endpos_k_, _menhir_s, (k : 'tv_assert_kw), _startpos_k_), _endpos_ps_, _, (ps : 'tv_list_params_), _startpos_ps_), _endpos_t_, _, (t : 'tv_term), _startpos_t_), _endpos_u_, _, (u : 'tv_term), _startpos_u_) = _menhir_stack in
        let _startpos = _startpos_k_ in
        let _endpos = _endpos_u_ in
        let _v : 'tv_query = let _endpos = _endpos_u_ in
        let _symbolstartpos = _startpos_k_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 221 "src/parsing/lpParser.mly"
    ( let t = make_abst _startpos_ps_ ps t _endpos_t_ in
      let u = make_abst _startpos_ps_ ps u _endpos_u_ in
      make_pos _sloc (P_query_assert(k, P_assert_conv(t, u))) )
# 2595 "src/parsing/lpParser.ml"
         in
        _menhir_goto_query _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv788)) : 'freshtv790)
    | MenhirState236 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv793 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv791 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((((_menhir_stack, _endpos_k_, _menhir_s, (k : 'tv_assert_kw), _startpos_k_), _endpos_ps_, _, (ps : 'tv_list_params_), _startpos_ps_), _endpos_t_, _, (t : 'tv_term), _startpos_t_), _endpos_a_, _, (a : 'tv_term), _startpos_a_) = _menhir_stack in
        let _startpos = _startpos_k_ in
        let _endpos = _endpos_a_ in
        let _v : 'tv_query = let _endpos = _endpos_a_ in
        let _symbolstartpos = _startpos_k_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 217 "src/parsing/lpParser.mly"
    ( let t = make_abst _startpos_ps_ ps t _endpos_t_ in
      let a = make_prod _startpos_ps_ ps a _endpos_a_ in
      make_pos _sloc (P_query_assert(k, P_assert_typing(t, a))) )
# 2614 "src/parsing/lpParser.ml"
         in
        _menhir_goto_query _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv792)) : 'freshtv794)
    | MenhirState247 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv797 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.BEGIN ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState250
        | LpLexer.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv795 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _endpos_t_, _menhir_s, (t : 'tv_term), _startpos_t_) = _menhir_stack in
            let _v : 'tv_term_proof = 
# 255 "src/parsing/lpParser.mly"
           ( Some t, None )
# 2632 "src/parsing/lpParser.ml"
             in
            _menhir_goto_term_proof _menhir_env _menhir_stack _menhir_s _v) : 'freshtv796)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState250) : 'freshtv798)
    | MenhirState257 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv811 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.ASSIGN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv807 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.VBAR ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv801) = Obj.magic _menhir_stack in
                let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv799) = Obj.magic _menhir_stack in
                let (_endpos_x_ : Lexing.position) = _endpos in
                ((let x = () in
                let _endpos = _endpos_x_ in
                let _v : 'tv_option_VBAR_ = 
# 116 "<standard.mly>"
    ( Some x )
# 2666 "src/parsing/lpParser.ml"
                 in
                _menhir_goto_option_VBAR_ _menhir_env _menhir_stack _endpos _v) : 'freshtv800)) : 'freshtv802)
            | LpLexer.SEMICOLON | LpLexer.UID _ | LpLexer.WITH ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv803) = Obj.magic _menhir_stack in
                ((let (_, _endpos) = Obj.magic _menhir_stack in
                let _v : 'tv_option_VBAR_ = 
# 114 "<standard.mly>"
    ( None )
# 2676 "src/parsing/lpParser.ml"
                 in
                _menhir_goto_option_VBAR_ _menhir_env _menhir_stack _endpos _v) : 'freshtv804)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (((('freshtv805 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv806)) : 'freshtv808)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv809 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv810)) : 'freshtv812)
    | MenhirState264 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv825 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv823 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _endpos_i_, _menhir_s, (i : 'tv_uid), _startpos_i_), _endpos_ps_, _, (ps : 'tv_list_params_), _startpos_ps_), _endpos_t_, _, (t : 'tv_term), _startpos_t_) = _menhir_stack in
        let _endpos = _endpos_t_ in
        let _v : 'tv_constructor = 
# 246 "src/parsing/lpParser.mly"
    ( (i, make_prod _startpos_ps_ ps t _endpos_t_) )
# 2703 "src/parsing/lpParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv821) = _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_constructor) = _v in
        ((let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv819 * Lexing.position * _menhir_state * 'tv_constructor) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.VBAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv813 * Lexing.position * _menhir_state * 'tv_constructor) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState269 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState269) : 'freshtv814)
        | LpLexer.SEMICOLON | LpLexer.WITH ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv815 * Lexing.position * _menhir_state * 'tv_constructor) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_constructor)) = _menhir_stack in
            let _endpos = _endpos_x_ in
            let _v : 'tv_separated_nonempty_list_VBAR_constructor_ = 
# 241 "<standard.mly>"
    ( [ x ] )
# 2738 "src/parsing/lpParser.ml"
             in
            _menhir_goto_separated_nonempty_list_VBAR_constructor_ _menhir_env _menhir_stack _endpos _menhir_s _v) : 'freshtv816)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv817 * Lexing.position * _menhir_state * 'tv_constructor) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv818)) : 'freshtv820)) : 'freshtv822)) : 'freshtv824)) : 'freshtv826)
    | _ ->
        _menhir_fail ()

and _menhir_reduce45 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_list_terminated_tactic_SEMICOLON__ = 
# 211 "<standard.mly>"
    ( [] )
# 2756 "src/parsing/lpParser.ml"
     in
    _menhir_goto_list_terminated_tactic_SEMICOLON__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run178 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.STRINGLIT _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv599) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_v : (
# 88 "src/parsing/lpParser.mly"
       (string)
# 2773 "src/parsing/lpParser.ml"
        )) = _v in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv597) = Obj.magic _menhir_stack in
        let (_endpos_x_ : Lexing.position) = _endpos in
        let ((x : (
# 88 "src/parsing/lpParser.mly"
       (string)
# 2782 "src/parsing/lpParser.ml"
        )) : (
# 88 "src/parsing/lpParser.mly"
       (string)
# 2786 "src/parsing/lpParser.ml"
        )) = _v in
        ((let _endpos = _endpos_x_ in
        let _v : 'tv_option_STRINGLIT_ = 
# 116 "<standard.mly>"
    ( Some x )
# 2792 "src/parsing/lpParser.ml"
         in
        _menhir_goto_option_STRINGLIT_ _menhir_env _menhir_stack _endpos _v) : 'freshtv598)) : 'freshtv600)
    | LpLexer.SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv601) = Obj.magic _menhir_stack in
        ((let (_, _endpos) = Obj.magic _menhir_stack in
        let _v : 'tv_option_STRINGLIT_ = 
# 114 "<standard.mly>"
    ( None )
# 2802 "src/parsing/lpParser.ml"
         in
        _menhir_goto_option_STRINGLIT_ _menhir_env _menhir_stack _endpos _v) : 'freshtv602)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv603 * Lexing.position * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv604)

and _menhir_run181 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv595) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _v : 'tv_tactic = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 187 "src/parsing/lpParser.mly"
             ( make_pos _sloc P_tac_sym )
# 2827 "src/parsing/lpParser.ml"
     in
    _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv596)

and _menhir_run182 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv593) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _v : 'tv_tactic = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 186 "src/parsing/lpParser.mly"
          ( make_pos _sloc P_tac_solve )
# 2845 "src/parsing/lpParser.ml"
     in
    _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv594)

and _menhir_run183 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.QID _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState183 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState183 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.SEMICOLON ->
        _menhir_reduce76 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState183

and _menhir_run185 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.ASSOC _v ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.BACKQUOTE | LpLexer.ID_EXPL _ | LpLexer.INT _ | LpLexer.LAMBDA | LpLexer.LET | LpLexer.L_CU_BRACKET | LpLexer.L_PAREN | LpLexer.L_SQ_BRACKET | LpLexer.PI | LpLexer.QID _ | LpLexer.TYPE_TERM | LpLexer.UID _ | LpLexer.UID_META _ | LpLexer.UID_PAT _ | LpLexer.WILD ->
        _menhir_reduce66 _menhir_env (Obj.magic _menhir_stack) MenhirState185
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState185

and _menhir_run208 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv591) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _v : 'tv_tactic = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 181 "src/parsing/lpParser.mly"
                ( make_pos _sloc P_tac_refl )
# 2895 "src/parsing/lpParser.ml"
     in
    _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv592)

and _menhir_run209 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.BACKQUOTE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ID_EXPL _v ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState209 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.INT _v ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState209 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LAMBDA ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LET ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_CU_BRACKET ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_PAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PI ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.QID _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState209 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.TYPE_TERM ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState209 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState209 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_META _v ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState209 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_PAT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState209 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState209 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState209

and _menhir_run211 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv589) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _v : 'tv_tactic = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 179 "src/parsing/lpParser.mly"
              ( make_pos _sloc P_tac_induction )
# 2952 "src/parsing/lpParser.ml"
     in
    _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv590)

and _menhir_run212 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.UID _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState212 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState212

and _menhir_run216 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.UID _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState216 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState216

and _menhir_run218 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.INT _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv585 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_v : (
# 86 "src/parsing/lpParser.mly"
       (int)
# 2995 "src/parsing/lpParser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv583 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_i_ : Lexing.position) = _endpos in
        let ((i : (
# 86 "src/parsing/lpParser.mly"
       (int)
# 3005 "src/parsing/lpParser.ml"
        )) : (
# 86 "src/parsing/lpParser.mly"
       (int)
# 3009 "src/parsing/lpParser.ml"
        )) = _v in
        let (_startpos_i_ : Lexing.position) = _startpos in
        ((let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _v : 'tv_tactic = let _endpos = _endpos_i_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 176 "src/parsing/lpParser.mly"
                ( make_pos _sloc (P_tac_focus i) )
# 3019 "src/parsing/lpParser.ml"
         in
        _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv584)) : 'freshtv586)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv587 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv588)

and _menhir_run220 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv581) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _v : 'tv_tactic = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 175 "src/parsing/lpParser.mly"
         ( make_pos _sloc P_tac_fail )
# 3044 "src/parsing/lpParser.ml"
     in
    _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv582)

and _menhir_run221 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.UID _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState221 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState221 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState221

and _menhir_run223 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.BACKQUOTE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ID_EXPL _v ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState223 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.INT _v ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState223 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LAMBDA ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LET ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_CU_BRACKET ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_PAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PI ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.QID _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState223 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.TYPE_TERM ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState223 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState223 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_META _v ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState223 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_PAT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState223 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState223 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState223

and _menhir_run225 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv579) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _v : 'tv_tactic = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 172 "src/parsing/lpParser.mly"
          ( make_pos _sloc P_tac_admit )
# 3116 "src/parsing/lpParser.ml"
     in
    _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv580)

and _menhir_goto_list_params_ : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_list_params_ -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState60 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv547 * Lexing.position * _menhir_state * 'tv_params * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv545 * Lexing.position * _menhir_state * 'tv_params * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_params), _startpos_x_), _endpos_xs_, _, (xs : 'tv_list_params_), _startpos_xs_) = _menhir_stack in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_xs_ in
        let _v : 'tv_list_params_ = 
# 213 "<standard.mly>"
    ( x :: xs )
# 3135 "src/parsing/lpParser.ml"
         in
        _menhir_goto_list_params_ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv546)) : 'freshtv548)
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv549 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.COLON ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | LpLexer.ASSIGN ->
            _menhir_reduce78 _menhir_env (Obj.magic _menhir_stack) MenhirState62
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState62) : 'freshtv550)
    | MenhirState173 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv553 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv551 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState174 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState175) : 'freshtv552)
        | LpLexer.ASSIGN ->
            _menhir_reduce78 _menhir_env (Obj.magic _menhir_stack) MenhirState174
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState174) : 'freshtv554)
    | MenhirState230 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv559 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.TURNSTILE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv555 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState232 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState232 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState232 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState232 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState232 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState232 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState232 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState232 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState232 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState232 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState232 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState232 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState232 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState232 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState232) : 'freshtv556)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv557 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv558)) : 'freshtv560)
    | MenhirState171 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv565 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.INDUCTIVE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv561 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState254 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState254) : 'freshtv562)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv563 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv564)) : 'freshtv566)
    | MenhirState255 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv571 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv567 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState257 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState257 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState257 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState257 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState257 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState257 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState257) : 'freshtv568)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv569 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv570)) : 'freshtv572)
    | MenhirState262 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv577 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv573 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState264 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState264 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState264 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState264 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState264 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState264 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState264 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState264 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState264 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState264 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState264 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState264 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState264 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState264 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState264) : 'freshtv574)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv575 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv576)) : 'freshtv578)
    | _ ->
        _menhir_fail ()

and _menhir_goto_float_or_int : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_float_or_int -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState137 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv539) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_float_or_int) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv537) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((p : 'tv_float_or_int) : 'tv_float_or_int) = _v in
        ((let _v : (
# 126 "src/parsing/lpParser.mly"
      (Sign.notation)
# 3402 "src/parsing/lpParser.ml"
        ) = 
# 208 "src/parsing/lpParser.mly"
                          ( Prefix(p) )
# 3406 "src/parsing/lpParser.ml"
         in
        _menhir_goto_notation _menhir_env _menhir_stack _v) : 'freshtv538)) : 'freshtv540)
    | MenhirState143 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv543 * Lexing.position) * Lexing.position * _menhir_state * 'tv_option_ASSOC_ * Lexing.position) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_float_or_int) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv541 * Lexing.position) * Lexing.position * _menhir_state * 'tv_option_ASSOC_ * Lexing.position) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((p : 'tv_float_or_int) : 'tv_float_or_int) = _v in
        ((let ((_menhir_stack, _endpos__1_), _endpos_a_, _, (a : 'tv_option_ASSOC_), _startpos_a_) = _menhir_stack in
        let _v : (
# 126 "src/parsing/lpParser.mly"
      (Sign.notation)
# 3422 "src/parsing/lpParser.ml"
        ) = 
# 207 "src/parsing/lpParser.mly"
                                  ( Infix(Option.get Pratter.Neither a, p) )
# 3426 "src/parsing/lpParser.ml"
         in
        _menhir_goto_notation _menhir_env _menhir_stack _v) : 'freshtv542)) : 'freshtv544)
    | _ ->
        _menhir_fail ()

and _menhir_goto_option_env_ : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_option_env_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    match _menhir_s with
    | MenhirState44 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv531 * Lexing.position * _menhir_state * 'tv_patt_id * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_option_env_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv529 * Lexing.position * _menhir_state * 'tv_patt_id * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_e_ : Lexing.position) = _endpos in
        let (_ : _menhir_state) = _menhir_s in
        let ((e : 'tv_option_env_) : 'tv_option_env_) = _v in
        ((let (_menhir_stack, _endpos_p_, _menhir_s, (p : 'tv_patt_id), _startpos_p_) = _menhir_stack in
        let _startpos = _startpos_p_ in
        let _endpos = _endpos_e_ in
        let _v : 'tv_aterm = let _endpos = _endpos_e_ in
        let _symbolstartpos = _startpos_p_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 301 "src/parsing/lpParser.mly"
                     ( make_pos _sloc (P_Patt(p,Option.map Array.of_list e)) )
# 3455 "src/parsing/lpParser.ml"
         in
        _menhir_goto_aterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv530)) : 'freshtv532)
    | MenhirState6 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv535 * Lexing.position * _menhir_state * (
# 116 "src/parsing/lpParser.mly"
       (Syntax.meta_ident)
# 3463 "src/parsing/lpParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_option_env_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv533 * Lexing.position * _menhir_state * (
# 116 "src/parsing/lpParser.mly"
       (Syntax.meta_ident)
# 3472 "src/parsing/lpParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_e_ : Lexing.position) = _endpos in
        let (_ : _menhir_state) = _menhir_s in
        let ((e : 'tv_option_env_) : 'tv_option_env_) = _v in
        ((let (_menhir_stack, _endpos_m_, _menhir_s, (m : (
# 116 "src/parsing/lpParser.mly"
       (Syntax.meta_ident)
# 3480 "src/parsing/lpParser.ml"
        )), _startpos_m_) = _menhir_stack in
        let _startpos = _startpos_m_ in
        let _endpos = _endpos_e_ in
        let _v : 'tv_aterm = let _endpos = _endpos_e_ in
        let _symbolstartpos = _startpos_m_ in
        let _loc_m_ = (_startpos_m_, _endpos_m_) in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 299 "src/parsing/lpParser.mly"
      ( let mid = make_pos _loc_m_ m in
        make_pos _sloc (P_Meta(mid, Option.map Array.of_list e)) )
# 3492 "src/parsing/lpParser.ml"
         in
        _menhir_goto_aterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv534)) : 'freshtv536)
    | _ ->
        _menhir_fail ()

and _menhir_goto_loption_separated_nonempty_list_SEMICOLON_term__ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_loption_separated_nonempty_list_SEMICOLON_term__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv527 * _menhir_state) * _menhir_state * 'tv_loption_separated_nonempty_list_SEMICOLON_term__) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.R_SQ_BRACKET ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv523 * _menhir_state) * _menhir_state * 'tv_loption_separated_nonempty_list_SEMICOLON_term__) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv521 * _menhir_state) * _menhir_state * 'tv_loption_separated_nonempty_list_SEMICOLON_term__) = Obj.magic _menhir_stack in
        let (_endpos__3_ : Lexing.position) = _endpos in
        ((let ((_menhir_stack, _menhir_s), _, (xs : 'tv_loption_separated_nonempty_list_SEMICOLON_term__)) = _menhir_stack in
        let _endpos = _endpos__3_ in
        let _v : 'tv_env = let ts = 
# 232 "<standard.mly>"
    ( xs )
# 3519 "src/parsing/lpParser.ml"
         in
        
# 292 "src/parsing/lpParser.mly"
                                                                  ( ts )
# 3524 "src/parsing/lpParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv519) = _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_env) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv517) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_env) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv515) = Obj.magic _menhir_stack in
        let (_endpos_x_ : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((x : 'tv_env) : 'tv_env) = _v in
        ((let _endpos = _endpos_x_ in
        let _v : 'tv_option_env_ = 
# 116 "<standard.mly>"
    ( Some x )
# 3545 "src/parsing/lpParser.ml"
         in
        _menhir_goto_option_env_ _menhir_env _menhir_stack _endpos _menhir_s _v) : 'freshtv516)) : 'freshtv518)) : 'freshtv520)) : 'freshtv522)) : 'freshtv524)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv525 * _menhir_state) * _menhir_state * 'tv_loption_separated_nonempty_list_SEMICOLON_term__) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv526)) : 'freshtv528)

and _menhir_goto_param_id : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_param_id -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState221 | MenhirState24 | MenhirState16 | MenhirState14 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv505 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState16 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.WILD ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState16 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.COLON | LpLexer.R_CU_BRACKET | LpLexer.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv503 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_param_id), _startpos_x_) = _menhir_stack in
            let _endpos = _endpos_x_ in
            let _v : 'tv_nonempty_list_param_id_ = 
# 221 "<standard.mly>"
    ( [ x ] )
# 3578 "src/parsing/lpParser.ml"
             in
            _menhir_goto_nonempty_list_param_id_ _menhir_env _menhir_stack _endpos _menhir_s _v) : 'freshtv504)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16) : 'freshtv506)
    | MenhirState262 | MenhirState255 | MenhirState171 | MenhirState230 | MenhirState173 | MenhirState23 | MenhirState60 | MenhirState28 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv507 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position) = Obj.magic _menhir_stack in
        (_menhir_reduce86 _menhir_env (Obj.magic _menhir_stack) : 'freshtv508)
    | MenhirState11 | MenhirState36 | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv513 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv509 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState32 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState32) : 'freshtv510)
        | LpLexer.COMMA | LpLexer.L_CU_BRACKET | LpLexer.L_PAREN | LpLexer.UID _ | LpLexer.WILD ->
            _menhir_reduce86 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv511 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv512)) : 'freshtv514)
    | _ ->
        _menhir_fail ()

and _menhir_goto_saterm : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_saterm -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv501 * Lexing.position * _menhir_state * 'tv_saterm * Lexing.position) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.ARROW ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv497 * Lexing.position * _menhir_state * 'tv_saterm * Lexing.position) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState41 in
        ((let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.BACKQUOTE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.ID_EXPL _v ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState42 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.INT _v ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState42 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.LAMBDA ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.LET ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.L_CU_BRACKET ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.L_PAREN ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.PI ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.QID _v ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState42 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.TYPE_TERM ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID _v ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState42 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID_META _v ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState42 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID_PAT _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState42 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.WILD ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState42 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42) : 'freshtv498)
    | LpLexer.BACKQUOTE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ID_EXPL _v ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState41 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.INT _v ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState41 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LAMBDA ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LET ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_CU_BRACKET ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_PAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PI ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.QID _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState41 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.TYPE_TERM ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState41 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_META _v ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState41 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_PAT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState41 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState41 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.AS | LpLexer.ASSIGN | LpLexer.BEGIN | LpLexer.COLON | LpLexer.COMMA | LpLexer.EQUIV | LpLexer.HOOK_ARROW | LpLexer.IN | LpLexer.R_CU_BRACKET | LpLexer.R_PAREN | LpLexer.R_SQ_BRACKET | LpLexer.SEMICOLON | LpLexer.VBAR | LpLexer.WITH ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv499 * Lexing.position * _menhir_state * 'tv_saterm * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _endpos_t_, _menhir_s, (t : 'tv_saterm), _startpos_t_) = _menhir_stack in
        let _startpos = _startpos_t_ in
        let _endpos = _endpos_t_ in
        let _v : 'tv_term = 
# 321 "src/parsing/lpParser.mly"
             ( t )
# 3730 "src/parsing/lpParser.ml"
         in
        _menhir_goto_term _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv500)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState41) : 'freshtv502)

and _menhir_goto_tactic : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_tactic -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv495 * _menhir_state * 'tv_tactic) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv491 * _menhir_state * 'tv_tactic) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        ((let _menhir_stack = (_menhir_stack, _endpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.ADMIT ->
            _menhir_run225 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.APPLY ->
            _menhir_run223 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.ASSERT ->
            _menhir_run164 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.ASSERTNOT ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.ASSUME ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.COMPUTE ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.DEBUG ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.FAIL ->
            _menhir_run220 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.FLAG ->
            _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.FOCUS ->
            _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.GENERALIZE ->
            _menhir_run216 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.HAVE ->
            _menhir_run212 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.INDUCTION ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.PRINT ->
            _menhir_run127 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.PROOFTERM ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.PROVER ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.PROVER_TIMEOUT ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.REFINE ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.REFLEXIVITY ->
            _menhir_run208 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.REWRITE ->
            _menhir_run185 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.SIMPLIFY ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.SOLVE ->
            _menhir_run182 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.SYMMETRY ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.TYPE_QUERY ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.VERBOSE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.WHY3 ->
            _menhir_run178 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.ABORT | LpLexer.ADMITTED | LpLexer.END ->
            _menhir_reduce45 _menhir_env (Obj.magic _menhir_stack) MenhirState227
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState227) : 'freshtv492)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv493 * _menhir_state * 'tv_tactic) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv494)) : 'freshtv496)

and _menhir_goto_option_delimited_L_SQ_BRACKET_rw_patt_R_SQ_BRACKET__ : _menhir_env -> 'ttv_tail -> 'tv_option_delimited_L_SQ_BRACKET_rw_patt_R_SQ_BRACKET__ -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv489 * Lexing.position * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_option_ASSOC_ * Lexing.position) * 'tv_option_delimited_L_SQ_BRACKET_rw_patt_R_SQ_BRACKET__) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.BACKQUOTE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState206 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ID_EXPL _v ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState206 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.INT _v ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState206 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LAMBDA ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState206 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LET ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState206 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_CU_BRACKET ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState206 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_PAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState206 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PI ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState206 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.QID _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState206 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.TYPE_TERM ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState206 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState206 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_META _v ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState206 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_PAT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState206 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState206 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState206) : 'freshtv490)

and _menhir_reduce149 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (
# 115 "src/parsing/lpParser.mly"
       (string)
# 3864 "src/parsing/lpParser.ml"
) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_i_, _menhir_s, (i : (
# 115 "src/parsing/lpParser.mly"
       (string)
# 3870 "src/parsing/lpParser.ml"
    )), _startpos_i_) = _menhir_stack in
    let _startpos = _startpos_i_ in
    let _endpos = _endpos_i_ in
    let _v : 'tv_uid = let _endpos = _endpos_i_ in
    let _symbolstartpos = _startpos_i_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 130 "src/parsing/lpParser.mly"
           ( make_pos _sloc i)
# 3880 "src/parsing/lpParser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv487) = _menhir_stack in
    let (_endpos : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_uid) = _v in
    let (_startpos : Lexing.position) = _startpos in
    ((let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState262 | MenhirState255 | MenhirState171 | MenhirState230 | MenhirState221 | MenhirState173 | MenhirState11 | MenhirState60 | MenhirState23 | MenhirState36 | MenhirState28 | MenhirState27 | MenhirState24 | MenhirState16 | MenhirState14 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv447 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv445 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _endpos_i_, _menhir_s, (i : 'tv_uid), _startpos_i_) = _menhir_stack in
        let _startpos = _startpos_i_ in
        let _endpos = _endpos_i_ in
        let _v : 'tv_param_id = 
# 145 "src/parsing/lpParser.mly"
          ( Some i )
# 3901 "src/parsing/lpParser.ml"
         in
        _menhir_goto_param_id _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv446)) : 'freshtv448)
    | MenhirState22 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv449 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.L_CU_BRACKET ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.L_PAREN ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState23 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.WILD ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState23 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.ASSIGN | LpLexer.COLON ->
            _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState23
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23) : 'freshtv450)
    | MenhirState115 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv457 * _menhir_state * Lexing.position) * _menhir_state * 'tv_path) * _menhir_state) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv453 * _menhir_state * Lexing.position) * _menhir_state * 'tv_path) * _menhir_state) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv451 * _menhir_state * Lexing.position) * _menhir_state * 'tv_path) * _menhir_state) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__5_ : Lexing.position) = _endpos in
            ((let ((((_menhir_stack, _menhir_s, _startpos__1_), _, (i : 'tv_path)), _), _endpos_a_, _, (a : 'tv_uid), _startpos_a_) = _menhir_stack in
            let _v : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 3941 "src/parsing/lpParser.ml"
            ) = let _endpos = _endpos__5_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 265 "src/parsing/lpParser.mly"
    ( make_pos _sloc (P_require_as(i,a)) )
# 3948 "src/parsing/lpParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv452)) : 'freshtv454)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv455 * _menhir_state * Lexing.position) * _menhir_state * 'tv_path) * _menhir_state) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv456)) : 'freshtv458)
    | MenhirState172 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv459 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.L_CU_BRACKET ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.L_PAREN ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState173 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.WILD ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState173 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.ASSIGN | LpLexer.COLON ->
            _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState173
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState173) : 'freshtv460)
    | MenhirState188 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv465 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.IN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv461 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState191 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState191 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState191 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState191 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState191 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState191 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState191 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState191 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState191) : 'freshtv462)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv463 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv464)) : 'freshtv466)
    | MenhirState200 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv471 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.IN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv467 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState202) : 'freshtv468)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv469 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv470)) : 'freshtv472)
    | MenhirState212 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv477 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv473 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState214) : 'freshtv474)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv475 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv476)) : 'freshtv478)
    | MenhirState216 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv481 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv479 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_i_, _, (i : 'tv_uid), _startpos_i_) = _menhir_stack in
        let _v : 'tv_tactic = let _endpos = _endpos_i_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 177 "src/parsing/lpParser.mly"
                     ( make_pos _sloc (P_tac_generalize i) )
# 4147 "src/parsing/lpParser.ml"
         in
        _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv480)) : 'freshtv482)
    | MenhirState274 | MenhirState254 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv483 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.L_CU_BRACKET ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState255 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.L_PAREN ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState255 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState255 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.WILD ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState255 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.COLON ->
            _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState255
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState255) : 'freshtv484)
    | MenhirState269 | MenhirState261 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv485 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.L_CU_BRACKET ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState262 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.L_PAREN ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState262 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState262 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.WILD ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState262 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.COLON ->
            _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState262
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState262) : 'freshtv486)
    | _ ->
        _menhir_fail ()) : 'freshtv488)

and _menhir_reduce41 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let (_, _startpos) = Obj.magic _menhir_stack in
    let _endpos = _startpos in
    let _v : 'tv_list_params_ = 
# 211 "<standard.mly>"
    ( [] )
# 4200 "src/parsing/lpParser.ml"
     in
    _menhir_goto_list_params_ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_goto_notation : _menhir_env -> 'ttv_tail -> (
# 126 "src/parsing/lpParser.mly"
      (Sign.notation)
# 4207 "src/parsing/lpParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv443 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 4215 "src/parsing/lpParser.ml"
    ) * Lexing.position) * (
# 126 "src/parsing/lpParser.mly"
      (Sign.notation)
# 4219 "src/parsing/lpParser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv439 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 4229 "src/parsing/lpParser.ml"
        ) * Lexing.position) * (
# 126 "src/parsing/lpParser.mly"
      (Sign.notation)
# 4233 "src/parsing/lpParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv437 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 4240 "src/parsing/lpParser.ml"
        ) * Lexing.position) * (
# 126 "src/parsing/lpParser.mly"
      (Sign.notation)
# 4244 "src/parsing/lpParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_endpos__4_ : Lexing.position) = _endpos in
        ((let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos_i_, _, (i : (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 4250 "src/parsing/lpParser.ml"
        )), _startpos_i_), (n : (
# 126 "src/parsing/lpParser.mly"
      (Sign.notation)
# 4254 "src/parsing/lpParser.ml"
        ))) = _menhir_stack in
        let _v : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 4259 "src/parsing/lpParser.ml"
        ) = let _endpos = _endpos__4_ in
        let _startpos = _startpos__1_ in
        let _loc = (_startpos, _endpos) in
        
# 288 "src/parsing/lpParser.mly"
                                       ( make_pos _loc (P_notation(i,n)) )
# 4266 "src/parsing/lpParser.ml"
         in
        _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv438)) : 'freshtv440)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv441 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 4276 "src/parsing/lpParser.ml"
        ) * Lexing.position) * (
# 126 "src/parsing/lpParser.mly"
      (Sign.notation)
# 4280 "src/parsing/lpParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv442)) : 'freshtv444)

and _menhir_run138 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 86 "src/parsing/lpParser.mly"
       (int)
# 4288 "src/parsing/lpParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv435) = Obj.magic _menhir_stack in
    let (_endpos_n_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((n : (
# 86 "src/parsing/lpParser.mly"
       (int)
# 4299 "src/parsing/lpParser.ml"
    )) : (
# 86 "src/parsing/lpParser.mly"
       (int)
# 4303 "src/parsing/lpParser.ml"
    )) = _v in
    let (_startpos_n_ : Lexing.position) = _startpos in
    ((let _v : 'tv_float_or_int = 
# 204 "src/parsing/lpParser.mly"
            ( float_of_int n )
# 4309 "src/parsing/lpParser.ml"
     in
    _menhir_goto_float_or_int _menhir_env _menhir_stack _menhir_s _v) : 'freshtv436)

and _menhir_run139 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 87 "src/parsing/lpParser.mly"
       (float)
# 4316 "src/parsing/lpParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv433) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((p : (
# 87 "src/parsing/lpParser.mly"
       (float)
# 4326 "src/parsing/lpParser.ml"
    )) : (
# 87 "src/parsing/lpParser.mly"
       (float)
# 4330 "src/parsing/lpParser.ml"
    )) = _v in
    ((let _v : 'tv_float_or_int = 
# 203 "src/parsing/lpParser.mly"
            ( p )
# 4335 "src/parsing/lpParser.ml"
     in
    _menhir_goto_float_or_int _menhir_env _menhir_stack _menhir_s _v) : 'freshtv434)

and _menhir_goto_option_id_ : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_option_id_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    match _menhir_s with
    | MenhirState127 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv427 * Lexing.position * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_option_id_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv425 * Lexing.position * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_i_ : Lexing.position) = _endpos in
        let (_ : _menhir_state) = _menhir_s in
        let ((i : 'tv_option_id_) : 'tv_option_id_) = _v in
        ((let (_menhir_stack, _endpos__1_, _menhir_s, _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_i_ in
        let _v : 'tv_query = let _endpos = _endpos_i_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 226 "src/parsing/lpParser.mly"
                ( make_pos _sloc (P_query_print i) )
# 4362 "src/parsing/lpParser.ml"
         in
        _menhir_goto_query _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv426)) : 'freshtv428)
    | MenhirState183 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv431 * Lexing.position * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_option_id_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv429 * Lexing.position * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_i_ : Lexing.position) = _endpos in
        let (_ : _menhir_state) = _menhir_s in
        let ((i : 'tv_option_id_) : 'tv_option_id_) = _v in
        ((let (_menhir_stack, _endpos__1_, _menhir_s, _startpos__1_) = _menhir_stack in
        let _v : 'tv_tactic = let _endpos = _endpos_i_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 185 "src/parsing/lpParser.mly"
                   ( make_pos _sloc (P_tac_simpl i) )
# 4383 "src/parsing/lpParser.ml"
         in
        _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv430)) : 'freshtv432)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_modifier_ : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_list_modifier_ -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState169 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv419 * Lexing.position * _menhir_state * 'tv_modifier * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv417 * Lexing.position * _menhir_state * 'tv_modifier * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _endpos_x_, _menhir_s, (x : 'tv_modifier), _startpos_x_), _endpos_xs_, _, (xs : 'tv_list_modifier_), _startpos_xs_) = _menhir_stack in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_xs_ in
        let _v : 'tv_list_modifier_ = 
# 213 "<standard.mly>"
    ( x :: xs )
# 4404 "src/parsing/lpParser.ml"
         in
        _menhir_goto_list_modifier_ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv418)) : 'freshtv420)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv423 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.L_CU_BRACKET ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.L_PAREN ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.SYMBOL ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv421 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState171 in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState172 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState172) : 'freshtv422)
        | LpLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.WILD ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.INDUCTIVE ->
            _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState171
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState171) : 'freshtv424)
    | _ ->
        _menhir_fail ()

and _menhir_reduce74 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let (_, _endpos) = Obj.magic _menhir_stack in
    let _v : 'tv_option_env_ = 
# 114 "<standard.mly>"
    ( None )
# 4451 "src/parsing/lpParser.ml"
     in
    _menhir_goto_option_env_ _menhir_env _menhir_stack _endpos _menhir_s _v

and _menhir_run7 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.BACKQUOTE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ID_EXPL _v ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState7 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.INT _v ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState7 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LAMBDA ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LET ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_CU_BRACKET ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_PAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PI ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.QID _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState7 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.TYPE_TERM ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState7 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState7 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_META _v ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState7 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_PAT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState7 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState7 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.R_SQ_BRACKET ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv415) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState7 in
        ((let _v : 'tv_loption_separated_nonempty_list_SEMICOLON_term__ = 
# 142 "<standard.mly>"
    ( [] )
# 4496 "src/parsing/lpParser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_SEMICOLON_term__ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv416)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState7

and _menhir_run12 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv413) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_param_id = 
# 146 "src/parsing/lpParser.mly"
         ( None )
# 4517 "src/parsing/lpParser.ml"
     in
    _menhir_goto_param_id _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv414)

and _menhir_run14 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.UID _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState14 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState14 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState14

and _menhir_run24 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.UID _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState24 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState24 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState24

and _menhir_goto_aterm : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_aterm -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    match _menhir_s with
    | MenhirState257 | MenhirState264 | MenhirState247 | MenhirState175 | MenhirState232 | MenhirState236 | MenhirState234 | MenhirState223 | MenhirState214 | MenhirState209 | MenhirState206 | MenhirState187 | MenhirState202 | MenhirState195 | MenhirState197 | MenhirState188 | MenhirState191 | MenhirState155 | MenhirState98 | MenhirState105 | MenhirState100 | MenhirState95 | MenhirState3 | MenhirState89 | MenhirState93 | MenhirState85 | MenhirState7 | MenhirState76 | MenhirState19 | MenhirState20 | MenhirState21 | MenhirState64 | MenhirState66 | MenhirState26 | MenhirState32 | MenhirState54 | MenhirState38 | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv407) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_aterm) = _v in
        let (_startpos : Lexing.position) = _startpos in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv405) = Obj.magic _menhir_stack in
        let (_endpos_t_ : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((t : 'tv_aterm) : 'tv_aterm) = _v in
        let (_startpos_t_ : Lexing.position) = _startpos in
        ((let _startpos = _startpos_t_ in
        let _endpos = _endpos_t_ in
        let _v : 'tv_saterm = 
# 308 "src/parsing/lpParser.mly"
            ( t )
# 4572 "src/parsing/lpParser.ml"
         in
        _menhir_goto_saterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv406)) : 'freshtv408)
    | MenhirState41 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv411 * Lexing.position * _menhir_state * 'tv_saterm * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _endpos in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_aterm) = _v in
        let (_startpos : Lexing.position) = _startpos in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv409 * Lexing.position * _menhir_state * 'tv_saterm * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_u_ : Lexing.position) = _endpos in
        let (_ : _menhir_state) = _menhir_s in
        let ((u : 'tv_aterm) : 'tv_aterm) = _v in
        let (_startpos_u_ : Lexing.position) = _startpos in
        ((let (_menhir_stack, _endpos_t_, _menhir_s, (t : 'tv_saterm), _startpos_t_) = _menhir_stack in
        let _startpos = _startpos_t_ in
        let _endpos = _endpos_u_ in
        let _v : 'tv_saterm = let _endpos = _endpos_u_ in
        let _symbolstartpos = _startpos_t_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 307 "src/parsing/lpParser.mly"
                     ( make_pos _sloc (P_Appl(t,u)) )
# 4597 "src/parsing/lpParser.ml"
         in
        _menhir_goto_saterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv410)) : 'freshtv412)
    | _ ->
        _menhir_fail ()

and _menhir_goto_term_id : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_term_id -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState35 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv399 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term_id * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.L_CU_BRACKET ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.L_PAREN ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState36 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.WILD ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState36 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36) : 'freshtv400)
    | MenhirState264 | MenhirState257 | MenhirState247 | MenhirState236 | MenhirState234 | MenhirState232 | MenhirState223 | MenhirState214 | MenhirState209 | MenhirState206 | MenhirState202 | MenhirState197 | MenhirState195 | MenhirState187 | MenhirState188 | MenhirState191 | MenhirState175 | MenhirState155 | MenhirState105 | MenhirState100 | MenhirState98 | MenhirState95 | MenhirState93 | MenhirState89 | MenhirState85 | MenhirState3 | MenhirState76 | MenhirState7 | MenhirState19 | MenhirState20 | MenhirState21 | MenhirState66 | MenhirState64 | MenhirState26 | MenhirState54 | MenhirState32 | MenhirState41 | MenhirState42 | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv403 * Lexing.position * _menhir_state * 'tv_term_id * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv401 * Lexing.position * _menhir_state * 'tv_term_id * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _endpos_ti_, _menhir_s, (ti : 'tv_term_id), _startpos_ti_) = _menhir_stack in
        let _startpos = _startpos_ti_ in
        let _endpos = _endpos_ti_ in
        let _v : 'tv_aterm = 
# 295 "src/parsing/lpParser.mly"
               ( ti )
# 4636 "src/parsing/lpParser.ml"
         in
        _menhir_goto_aterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv402)) : 'freshtv404)
    | _ ->
        _menhir_fail ()

and _menhir_reduce76 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let (_, _endpos) = Obj.magic _menhir_stack in
    let _v : 'tv_option_id_ = 
# 114 "<standard.mly>"
    ( None )
# 4648 "src/parsing/lpParser.ml"
     in
    _menhir_goto_option_id_ _menhir_env _menhir_stack _endpos _menhir_s _v

and _menhir_goto_list_path_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_list_path_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState114 | MenhirState110 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv373 * _menhir_state * 'tv_path) * _menhir_state * 'tv_list_path_) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv371 * _menhir_state * 'tv_path) * _menhir_state * 'tv_list_path_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (x : 'tv_path)), _, (xs : 'tv_list_path_)) = _menhir_stack in
        let _v : 'tv_list_path_ = 
# 213 "<standard.mly>"
    ( x :: xs )
# 4665 "src/parsing/lpParser.ml"
         in
        _menhir_goto_list_path_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv372)) : 'freshtv374)
    | MenhirState109 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv381 * _menhir_state * Lexing.position) * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_path_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv377 * _menhir_state * Lexing.position) * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_path_) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv375 * _menhir_state * Lexing.position) * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_path_) = Obj.magic _menhir_stack in
            let (_endpos__4_ : Lexing.position) = _endpos in
            ((let (((_menhir_stack, _menhir_s, _startpos__1_), _, _startpos__2_), _, (l : 'tv_list_path_)) = _menhir_stack in
            let _v : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 4685 "src/parsing/lpParser.ml"
            ) = let _endpos = _endpos__4_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 261 "src/parsing/lpParser.mly"
    ( make_pos _sloc (P_require(true,l)) )
# 4692 "src/parsing/lpParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv376)) : 'freshtv378)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv379 * _menhir_state * Lexing.position) * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_path_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv380)) : 'freshtv382)
    | MenhirState107 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv389 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_path_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv385 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_path_) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv383 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_path_) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _, (l : 'tv_list_path_)) = _menhir_stack in
            let _v : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 4719 "src/parsing/lpParser.ml"
            ) = let _endpos = _endpos__3_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 263 "src/parsing/lpParser.mly"
    ( make_pos _sloc (P_require(false,l)) )
# 4726 "src/parsing/lpParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv384)) : 'freshtv386)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv387 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_path_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv388)) : 'freshtv390)
    | MenhirState130 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv397 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_path_) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv393 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_path_) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv391 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_path_) = Obj.magic _menhir_stack in
            let (_endpos__3_ : Lexing.position) = _endpos in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _, (l : 'tv_list_path_)) = _menhir_stack in
            let _v : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 4753 "src/parsing/lpParser.ml"
            ) = let _endpos = _endpos__3_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 267 "src/parsing/lpParser.mly"
    ( make_pos _sloc (P_open l) )
# 4760 "src/parsing/lpParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv392)) : 'freshtv394)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv395 * _menhir_state * Lexing.position) * _menhir_state * 'tv_list_path_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv396)) : 'freshtv398)
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_run13 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 115 "src/parsing/lpParser.mly"
       (string)
# 4781 "src/parsing/lpParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce149 _menhir_env (Obj.magic _menhir_stack)

and _menhir_goto_query : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_query -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv365 * Lexing.position * _menhir_state * 'tv_query * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv361 * Lexing.position * _menhir_state * 'tv_query * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv359 * Lexing.position * _menhir_state * 'tv_query * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__2_ : Lexing.position) = _endpos in
            ((let (_menhir_stack, _endpos_q_, _menhir_s, (q : 'tv_query), _startpos_q_) = _menhir_stack in
            let _v : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 4809 "src/parsing/lpParser.ml"
            ) = let _endpos = _endpos__2_ in
            let _symbolstartpos = _startpos_q_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 289 "src/parsing/lpParser.mly"
                      ( make_pos _sloc (P_query(q)) )
# 4816 "src/parsing/lpParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv360)) : 'freshtv362)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv363 * Lexing.position * _menhir_state * 'tv_query * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv364)) : 'freshtv366)
    | MenhirState177 | MenhirState227 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv369 * Lexing.position * _menhir_state * 'tv_query * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv367 * Lexing.position * _menhir_state * 'tv_query * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _endpos_q_, _menhir_s, (q : 'tv_query), _startpos_q_) = _menhir_stack in
        let _v : 'tv_tactic = let _endpos = _endpos_q_ in
        let _symbolstartpos = _startpos_q_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 171 "src/parsing/lpParser.mly"
            ( make_pos _sloc (P_tac_query q) )
# 4838 "src/parsing/lpParser.ml"
         in
        _menhir_goto_tactic _menhir_env _menhir_stack _menhir_s _v) : 'freshtv368)) : 'freshtv370)
    | _ ->
        _menhir_fail ()

and _menhir_goto_modifier : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_modifier -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv357 * Lexing.position * _menhir_state * 'tv_modifier * Lexing.position) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.ASSOC _v ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState169 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.COMMUTATIVE ->
        _menhir_run157 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState169 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.CONSTANT ->
        _menhir_run154 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState169 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.INJECTIVE ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState169 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.OPAQUE ->
        _menhir_run133 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState169 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PRIVATE ->
        _menhir_run126 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState169 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PROTECTED ->
        _menhir_run124 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState169 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.SEQUENTIAL ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState169 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ASSOCIATIVE ->
        _menhir_reduce66 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | LpLexer.INDUCTIVE | LpLexer.L_CU_BRACKET | LpLexer.L_PAREN | LpLexer.SYMBOL | LpLexer.UID _ | LpLexer.WILD ->
        _menhir_reduce39 _menhir_env (Obj.magic _menhir_stack) MenhirState169
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState169) : 'freshtv358)

and _menhir_goto_option_ASSOC_ : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_option_ASSOC_ -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState141 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv333 * Lexing.position) * Lexing.position * _menhir_state * 'tv_option_ASSOC_ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.FLOAT _v ->
            _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
        | LpLexer.INT _v ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState143 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState143) : 'freshtv334)
    | MenhirState169 | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv341 * Lexing.position * _menhir_state * 'tv_option_ASSOC_ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.ASSOCIATIVE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv337 * Lexing.position * _menhir_state * 'tv_option_ASSOC_ * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv335 * Lexing.position * _menhir_state * 'tv_option_ASSOC_ * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__2_ : Lexing.position) = _endpos in
            let (_startpos__2_ : Lexing.position) = _startpos in
            ((let (_menhir_stack, _endpos_d_, _menhir_s, (d : 'tv_option_ASSOC_), _startpos_d_) = _menhir_stack in
            let _startpos = _startpos_d_ in
            let _endpos = _endpos__2_ in
            let _v : 'tv_modifier = let _endpos = _endpos__2_ in
            let _symbolstartpos = if _startpos_d_ != _endpos_d_ then
              _startpos_d_
            else
              _startpos__2_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 192 "src/parsing/lpParser.mly"
    ( let b = match d with Some Pratter.Left -> true | _ -> false in
      make_pos _sloc (P_prop (Term.Assoc b)) )
# 4924 "src/parsing/lpParser.ml"
             in
            _menhir_goto_modifier _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv336)) : 'freshtv338)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv339 * Lexing.position * _menhir_state * 'tv_option_ASSOC_ * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv340)) : 'freshtv342)
    | MenhirState185 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv355 * Lexing.position * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_option_ASSOC_ * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.L_SQ_BRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv349) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.BACKQUOTE ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.ID_EXPL _v ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState187 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.IN ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv347) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = MenhirState187 in
                let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                ((let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | LpLexer.BACKQUOTE ->
                    _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.ID_EXPL _v ->
                    _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.INT _v ->
                    _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.LAMBDA ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.LET ->
                    _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.L_CU_BRACKET ->
                    _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.L_PAREN ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.PI ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.QID _v ->
                    _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.TYPE_TERM ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.UID _v ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : 'freshtv345) = Obj.magic _menhir_stack in
                    let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                    let (_menhir_s : _menhir_state) = MenhirState188 in
                    let (_v : (
# 115 "src/parsing/lpParser.mly"
       (string)
# 4987 "src/parsing/lpParser.ml"
                    )) = _v in
                    let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                    ((let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | LpLexer.IN ->
                        _menhir_reduce149 _menhir_env (Obj.magic _menhir_stack)
                    | LpLexer.ARROW | LpLexer.BACKQUOTE | LpLexer.ID_EXPL _ | LpLexer.INT _ | LpLexer.LAMBDA | LpLexer.LET | LpLexer.L_CU_BRACKET | LpLexer.L_PAREN | LpLexer.PI | LpLexer.QID _ | LpLexer.R_SQ_BRACKET | LpLexer.TYPE_TERM | LpLexer.UID _ | LpLexer.UID_META _ | LpLexer.UID_PAT _ | LpLexer.WILD ->
                        _menhir_reduce37 _menhir_env (Obj.magic _menhir_stack)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let (_menhir_env : _menhir_env) = _menhir_env in
                        let (_menhir_stack : 'freshtv343 * Lexing.position * _menhir_state * (
# 115 "src/parsing/lpParser.mly"
       (string)
# 5005 "src/parsing/lpParser.ml"
                        ) * Lexing.position) = Obj.magic _menhir_stack in
                        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv344)) : 'freshtv346)
                | LpLexer.UID_META _v ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.UID_PAT _v ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.WILD ->
                    _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState188 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState188) : 'freshtv348)
            | LpLexer.INT _v ->
                _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState187 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LAMBDA ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.LET ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_CU_BRACKET ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.L_PAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.PI ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.QID _v ->
                _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState187 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.TYPE_TERM ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID _v ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState187 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_META _v ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState187 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.UID_PAT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState187 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.WILD ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState187 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState187) : 'freshtv350)
        | LpLexer.BACKQUOTE | LpLexer.ID_EXPL _ | LpLexer.INT _ | LpLexer.LAMBDA | LpLexer.LET | LpLexer.L_CU_BRACKET | LpLexer.L_PAREN | LpLexer.PI | LpLexer.QID _ | LpLexer.TYPE_TERM | LpLexer.UID _ | LpLexer.UID_META _ | LpLexer.UID_PAT _ | LpLexer.WILD ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv351) = Obj.magic _menhir_stack in
            ((let _v : 'tv_option_delimited_L_SQ_BRACKET_rw_patt_R_SQ_BRACKET__ = 
# 114 "<standard.mly>"
    ( None )
# 5053 "src/parsing/lpParser.ml"
             in
            _menhir_goto_option_delimited_L_SQ_BRACKET_rw_patt_R_SQ_BRACKET__ _menhir_env _menhir_stack _v) : 'freshtv352)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv353 * Lexing.position * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_option_ASSOC_ * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv354)) : 'freshtv356)
    | _ ->
        _menhir_fail ()

and _menhir_goto_assert_kw : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> 'tv_assert_kw -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv331 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.L_CU_BRACKET ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState230 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_PAREN ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState230 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState230 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState230 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.TURNSTILE ->
        _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState230
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState230) : 'freshtv332)

and _menhir_goto_id : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5092 "src/parsing/lpParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState257 | MenhirState264 | MenhirState247 | MenhirState175 | MenhirState232 | MenhirState236 | MenhirState234 | MenhirState223 | MenhirState214 | MenhirState209 | MenhirState206 | MenhirState187 | MenhirState202 | MenhirState195 | MenhirState197 | MenhirState188 | MenhirState191 | MenhirState155 | MenhirState98 | MenhirState105 | MenhirState100 | MenhirState95 | MenhirState93 | MenhirState89 | MenhirState3 | MenhirState85 | MenhirState7 | MenhirState76 | MenhirState19 | MenhirState20 | MenhirState21 | MenhirState64 | MenhirState66 | MenhirState26 | MenhirState32 | MenhirState54 | MenhirState35 | MenhirState38 | MenhirState41 | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv301 * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5102 "src/parsing/lpParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv299 * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5108 "src/parsing/lpParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _endpos_i_, _menhir_s, (i : (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5113 "src/parsing/lpParser.ml"
        )), _startpos_i_) = _menhir_stack in
        let _startpos = _startpos_i_ in
        let _endpos = _endpos_i_ in
        let _v : 'tv_term_id = let _endpos = _endpos_i_ in
        let _symbolstartpos = _startpos_i_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 139 "src/parsing/lpParser.mly"
         ( make_pos _sloc (P_Iden(i, false)) )
# 5123 "src/parsing/lpParser.ml"
         in
        _menhir_goto_term_id _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv300)) : 'freshtv302)
    | MenhirState183 | MenhirState127 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv305 * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5131 "src/parsing/lpParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv303 * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5137 "src/parsing/lpParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _endpos_x_, _menhir_s, (x : (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5142 "src/parsing/lpParser.ml"
        )), _startpos_x_) = _menhir_stack in
        let _endpos = _endpos_x_ in
        let _v : 'tv_option_id_ = 
# 116 "<standard.mly>"
    ( Some x )
# 5148 "src/parsing/lpParser.ml"
         in
        _menhir_goto_option_id_ _menhir_env _menhir_stack _endpos _menhir_s _v) : 'freshtv304)) : 'freshtv306)
    | MenhirState134 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv317 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5156 "src/parsing/lpParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.INFIX ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv307) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.ASSOC _v ->
                _menhir_run142 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState141 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.FLOAT _ | LpLexer.INT _ ->
                _menhir_reduce66 _menhir_env (Obj.magic _menhir_stack) MenhirState141
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState141) : 'freshtv308)
        | LpLexer.PREFIX ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv309) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.FLOAT _v ->
                _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _v
            | LpLexer.INT _v ->
                _menhir_run138 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState137 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState137) : 'freshtv310)
        | LpLexer.QUANTIFIER ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv313) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv311) = Obj.magic _menhir_stack in
            ((let _v : (
# 126 "src/parsing/lpParser.mly"
      (Sign.notation)
# 5200 "src/parsing/lpParser.ml"
            ) = 
# 209 "src/parsing/lpParser.mly"
               ( Quant )
# 5204 "src/parsing/lpParser.ml"
             in
            _menhir_goto_notation _menhir_env _menhir_stack _v) : 'freshtv312)) : 'freshtv314)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv315 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5214 "src/parsing/lpParser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv316)) : 'freshtv318)
    | MenhirState160 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv325 * _menhir_state * Lexing.position) * Lexing.position * (
# 88 "src/parsing/lpParser.mly"
       (string)
# 5223 "src/parsing/lpParser.ml"
        )) * Lexing.position) * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5227 "src/parsing/lpParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv321 * _menhir_state * Lexing.position) * Lexing.position * (
# 88 "src/parsing/lpParser.mly"
       (string)
# 5237 "src/parsing/lpParser.ml"
            )) * Lexing.position) * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5241 "src/parsing/lpParser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv319 * _menhir_state * Lexing.position) * Lexing.position * (
# 88 "src/parsing/lpParser.mly"
       (string)
# 5248 "src/parsing/lpParser.ml"
            )) * Lexing.position) * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5252 "src/parsing/lpParser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos__5_ : Lexing.position) = _endpos in
            ((let ((((_menhir_stack, _menhir_s, _startpos__1_), _endpos_s_, (s : (
# 88 "src/parsing/lpParser.mly"
       (string)
# 5258 "src/parsing/lpParser.ml"
            ))), _endpos__3_), _endpos_i_, _, (i : (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5262 "src/parsing/lpParser.ml"
            )), _startpos_i_) = _menhir_stack in
            let _v : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 5267 "src/parsing/lpParser.ml"
            ) = let _endpos = _endpos__5_ in
            let _startpos = _startpos__1_ in
            let _loc = (_startpos, _endpos) in
            
# 286 "src/parsing/lpParser.mly"
    ( make_pos _loc (P_builtin(s,i)) )
# 5274 "src/parsing/lpParser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv320)) : 'freshtv322)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv323 * _menhir_state * Lexing.position) * Lexing.position * (
# 88 "src/parsing/lpParser.mly"
       (string)
# 5284 "src/parsing/lpParser.ml"
            )) * Lexing.position) * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5288 "src/parsing/lpParser.ml"
            ) * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv324)) : 'freshtv326)
    | MenhirState277 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv329 * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5297 "src/parsing/lpParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv327 * Lexing.position * _menhir_state * (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5303 "src/parsing/lpParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 5308 "src/parsing/lpParser.ml"
        )), _startpos__1_) = _menhir_stack in
        Obj.magic _1) : 'freshtv328)) : 'freshtv330)
    | _ ->
        _menhir_fail ()

and _menhir_reduce39 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let (_, _startpos) = Obj.magic _menhir_stack in
    let _endpos = _startpos in
    let _v : 'tv_list_modifier_ = 
# 211 "<standard.mly>"
    ( [] )
# 5321 "src/parsing/lpParser.ml"
     in
    _menhir_goto_list_modifier_ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_reduce66 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let (_, _startpos) = Obj.magic _menhir_stack in
    let _endpos = _startpos in
    let _v : 'tv_option_ASSOC_ = 
# 114 "<standard.mly>"
    ( None )
# 5332 "src/parsing/lpParser.ml"
     in
    _menhir_goto_option_ASSOC_ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.INT _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv295 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_v : (
# 86 "src/parsing/lpParser.mly"
       (int)
# 5349 "src/parsing/lpParser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv293 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_i_ : Lexing.position) = _endpos in
        let ((i : (
# 86 "src/parsing/lpParser.mly"
       (int)
# 5359 "src/parsing/lpParser.ml"
        )) : (
# 86 "src/parsing/lpParser.mly"
       (int)
# 5363 "src/parsing/lpParser.ml"
        )) = _v in
        let (_startpos_i_ : Lexing.position) = _startpos in
        ((let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_i_ in
        let _v : 'tv_query = let _endpos = _endpos_i_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 233 "src/parsing/lpParser.mly"
                  ( make_pos _sloc (P_query_verbose(i)) )
# 5375 "src/parsing/lpParser.ml"
         in
        _menhir_goto_query _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv294)) : 'freshtv296)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv297 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv298)

and _menhir_run95 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.BACKQUOTE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ID_EXPL _v ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.INT _v ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LAMBDA ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LET ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_CU_BRACKET ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_PAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PI ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.QID _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.TYPE_TERM ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_META _v ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_PAT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState95

and _menhir_run97 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv291) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_modifier = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 200 "src/parsing/lpParser.mly"
               ( make_pos _sloc (P_mstrat Term.Sequen) )
# 5441 "src/parsing/lpParser.ml"
     in
    _menhir_goto_modifier _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv292)

and _menhir_run4 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv289) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_aterm = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 296 "src/parsing/lpParser.mly"
         ( make_pos _sloc P_Wild )
# 5461 "src/parsing/lpParser.ml"
     in
    _menhir_goto_aterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv290)

and _menhir_run5 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 117 "src/parsing/lpParser.mly"
       (string)
# 5468 "src/parsing/lpParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv287) = Obj.magic _menhir_stack in
    let (_endpos_p_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((p : (
# 117 "src/parsing/lpParser.mly"
       (string)
# 5479 "src/parsing/lpParser.ml"
    )) : (
# 117 "src/parsing/lpParser.mly"
       (string)
# 5483 "src/parsing/lpParser.ml"
    )) = _v in
    let (_startpos_p_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos_p_ in
    let _endpos = _endpos_p_ in
    let _v : 'tv_patt_id = let _endpos = _endpos_p_ in
    let _symbolstartpos = _startpos_p_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 142 "src/parsing/lpParser.mly"
                   ( if p = "_" then None else Some(make_pos _sloc p) )
# 5494 "src/parsing/lpParser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv285) = _menhir_stack in
    let (_endpos : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_patt_id) = _v in
    let (_startpos : Lexing.position) = _startpos in
    ((let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv283 * Lexing.position * _menhir_state * 'tv_patt_id * Lexing.position) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.L_SQ_BRACKET ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState44
    | LpLexer.ARROW | LpLexer.AS | LpLexer.ASSIGN | LpLexer.BACKQUOTE | LpLexer.BEGIN | LpLexer.COLON | LpLexer.COMMA | LpLexer.EQUIV | LpLexer.HOOK_ARROW | LpLexer.ID_EXPL _ | LpLexer.IN | LpLexer.INT _ | LpLexer.LAMBDA | LpLexer.LET | LpLexer.L_CU_BRACKET | LpLexer.L_PAREN | LpLexer.PI | LpLexer.QID _ | LpLexer.R_CU_BRACKET | LpLexer.R_PAREN | LpLexer.R_SQ_BRACKET | LpLexer.SEMICOLON | LpLexer.TYPE_TERM | LpLexer.UID _ | LpLexer.UID_META _ | LpLexer.UID_PAT _ | LpLexer.VBAR | LpLexer.WILD | LpLexer.WITH ->
        _menhir_reduce74 _menhir_env (Obj.magic _menhir_stack) MenhirState44
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState44) : 'freshtv284)) : 'freshtv286)) : 'freshtv288)

and _menhir_run6 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 116 "src/parsing/lpParser.mly"
       (Syntax.meta_ident)
# 5520 "src/parsing/lpParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.L_SQ_BRACKET ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState6
    | LpLexer.ARROW | LpLexer.AS | LpLexer.ASSIGN | LpLexer.BACKQUOTE | LpLexer.BEGIN | LpLexer.COLON | LpLexer.COMMA | LpLexer.EQUIV | LpLexer.HOOK_ARROW | LpLexer.ID_EXPL _ | LpLexer.IN | LpLexer.INT _ | LpLexer.LAMBDA | LpLexer.LET | LpLexer.L_CU_BRACKET | LpLexer.L_PAREN | LpLexer.PI | LpLexer.QID _ | LpLexer.R_CU_BRACKET | LpLexer.R_PAREN | LpLexer.R_SQ_BRACKET | LpLexer.SEMICOLON | LpLexer.TYPE_TERM | LpLexer.UID _ | LpLexer.UID_META _ | LpLexer.UID_PAT _ | LpLexer.VBAR | LpLexer.WILD | LpLexer.WITH ->
        _menhir_reduce74 _menhir_env (Obj.magic _menhir_stack) MenhirState6
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6

and _menhir_run9 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv281) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_aterm = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 297 "src/parsing/lpParser.mly"
              ( make_pos _sloc P_Type )
# 5552 "src/parsing/lpParser.ml"
     in
    _menhir_goto_aterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv282)

and _menhir_run11 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.L_CU_BRACKET ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState11 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_PAREN ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState11 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState11 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState11 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState11

and _menhir_run20 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.BACKQUOTE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ID_EXPL _v ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState20 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.INT _v ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState20 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LAMBDA ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LET ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_CU_BRACKET ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_PAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PI ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.QID _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState20 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.TYPE_TERM ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState20 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState20 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_META _v ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState20 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_PAT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState20 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState20 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20

and _menhir_run21 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.BACKQUOTE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ID_EXPL _v ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.INT _v ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LAMBDA ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LET ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_CU_BRACKET ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_PAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PI ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.QID _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.TYPE_TERM ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_META _v ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_PAT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState21 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState21

and _menhir_run22 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.UID _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState22 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState22

and _menhir_run27 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.L_CU_BRACKET ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_PAREN ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState27 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState27

and _menhir_run33 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 86 "src/parsing/lpParser.mly"
       (int)
# 5688 "src/parsing/lpParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv279) = Obj.magic _menhir_stack in
    let (_endpos_n_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((n : (
# 86 "src/parsing/lpParser.mly"
       (int)
# 5699 "src/parsing/lpParser.ml"
    )) : (
# 86 "src/parsing/lpParser.mly"
       (int)
# 5703 "src/parsing/lpParser.ml"
    )) = _v in
    let (_startpos_n_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos_n_ in
    let _endpos = _endpos_n_ in
    let _v : 'tv_aterm = let _endpos = _endpos_n_ in
    let _symbolstartpos = _startpos_n_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 304 "src/parsing/lpParser.mly"
          ( make_pos _sloc (P_NLit(n)) )
# 5714 "src/parsing/lpParser.ml"
     in
    _menhir_goto_aterm _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv280)

and _menhir_run34 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 119 "src/parsing/lpParser.mly"
       (Path.t)
# 5721 "src/parsing/lpParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv277) = Obj.magic _menhir_stack in
    let (_endpos_p_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((p : (
# 119 "src/parsing/lpParser.mly"
       (Path.t)
# 5732 "src/parsing/lpParser.ml"
    )) : (
# 119 "src/parsing/lpParser.mly"
       (Path.t)
# 5736 "src/parsing/lpParser.ml"
    )) = _v in
    let (_startpos_p_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos_p_ in
    let _endpos = _endpos_p_ in
    let _v : 'tv_term_id = let _endpos = _endpos_p_ in
    let _symbolstartpos = _startpos_p_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 140 "src/parsing/lpParser.mly"
              ( make_pos _sloc (P_Iden(qid_of_path _sloc p, true)) )
# 5747 "src/parsing/lpParser.ml"
     in
    _menhir_goto_term_id _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv278)

and _menhir_run35 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.ID_EXPL _v ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState35 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.QID _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState35 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState35 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState35

and _menhir_run120 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.INT _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv273 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_v : (
# 86 "src/parsing/lpParser.mly"
       (int)
# 5781 "src/parsing/lpParser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv271 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_i_ : Lexing.position) = _endpos in
        let ((i : (
# 86 "src/parsing/lpParser.mly"
       (int)
# 5791 "src/parsing/lpParser.ml"
        )) : (
# 86 "src/parsing/lpParser.mly"
       (int)
# 5795 "src/parsing/lpParser.ml"
        )) = _v in
        let (_startpos_i_ : Lexing.position) = _startpos in
        ((let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_i_ in
        let _v : 'tv_query = let _endpos = _endpos_i_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 232 "src/parsing/lpParser.mly"
                         ( make_pos _sloc (P_query_prover_timeout(i)) )
# 5807 "src/parsing/lpParser.ml"
         in
        _menhir_goto_query _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv272)) : 'freshtv274)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv275 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv276)

and _menhir_run122 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.STRINGLIT _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv267 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_v : (
# 88 "src/parsing/lpParser.mly"
       (string)
# 5831 "src/parsing/lpParser.ml"
        )) = _v in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv265 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_s_ : Lexing.position) = _endpos in
        let ((s : (
# 88 "src/parsing/lpParser.mly"
       (string)
# 5840 "src/parsing/lpParser.ml"
        )) : (
# 88 "src/parsing/lpParser.mly"
       (string)
# 5844 "src/parsing/lpParser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_s_ in
        let _v : 'tv_query = let _endpos = _endpos_s_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 231 "src/parsing/lpParser.mly"
                       ( make_pos _sloc (P_query_prover(s)) )
# 5855 "src/parsing/lpParser.ml"
         in
        _menhir_goto_query _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv266)) : 'freshtv268)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv269 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv270)

and _menhir_run124 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv263) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_modifier = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 199 "src/parsing/lpParser.mly"
              ( make_pos _sloc (P_expo Term.Protec) )
# 5882 "src/parsing/lpParser.ml"
     in
    _menhir_goto_modifier _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv264)

and _menhir_run125 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv261) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_query = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 227 "src/parsing/lpParser.mly"
              ( make_pos _sloc P_query_proofterm )
# 5902 "src/parsing/lpParser.ml"
     in
    _menhir_goto_query _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv262)

and _menhir_run126 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv259) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_modifier = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 198 "src/parsing/lpParser.mly"
            ( make_pos _sloc (P_expo Term.Privat) )
# 5922 "src/parsing/lpParser.ml"
     in
    _menhir_goto_modifier _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv260)

and _menhir_run127 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.QID _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.SEMICOLON ->
        _menhir_reduce76 _menhir_env (Obj.magic _menhir_stack) MenhirState127
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState127

and _menhir_reduce43 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_list_path_ = 
# 211 "<standard.mly>"
    ( [] )
# 5948 "src/parsing/lpParser.ml"
     in
    _menhir_goto_list_path_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run108 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 118 "src/parsing/lpParser.mly"
       (Path.t)
# 5955 "src/parsing/lpParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv257) = Obj.magic _menhir_stack in
    let (_endpos_i_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((i : (
# 118 "src/parsing/lpParser.mly"
       (Path.t)
# 5966 "src/parsing/lpParser.ml"
    )) : (
# 118 "src/parsing/lpParser.mly"
       (Path.t)
# 5970 "src/parsing/lpParser.ml"
    )) = _v in
    let (_startpos_i_ : Lexing.position) = _startpos in
    ((let _v : 'tv_path = let _endpos = _endpos_i_ in
    let _symbolstartpos = _startpos_i_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 136 "src/parsing/lpParser.mly"
            ( make_pos _sloc i)
# 5979 "src/parsing/lpParser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv255) = _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_path) = _v in
    ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState130 | MenhirState114 | MenhirState110 | MenhirState109 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv249 * _menhir_state * 'tv_path) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.QID _v ->
            _menhir_run108 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState110 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.SEMICOLON ->
            _menhir_reduce43 _menhir_env (Obj.magic _menhir_stack) MenhirState110
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState110) : 'freshtv250)
    | MenhirState107 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv253 * _menhir_state * Lexing.position) * _menhir_state * 'tv_path) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.AS ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv251 * _menhir_state * Lexing.position) * _menhir_state * 'tv_path) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState114 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.UID _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState115 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState115) : 'freshtv252)
        | LpLexer.QID _v ->
            _menhir_run108 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState114 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.SEMICOLON ->
            _menhir_reduce43 _menhir_env (Obj.magic _menhir_stack) MenhirState114
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState114) : 'freshtv254)
    | _ ->
        _menhir_fail ()) : 'freshtv256)) : 'freshtv258)

and _menhir_run133 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv247) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_modifier = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 197 "src/parsing/lpParser.mly"
           ( make_pos _sloc P_opaq )
# 6048 "src/parsing/lpParser.ml"
     in
    _menhir_goto_modifier _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv248)

and _menhir_run147 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv245) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_modifier = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 196 "src/parsing/lpParser.mly"
              ( make_pos _sloc (P_prop Term.Injec) )
# 6068 "src/parsing/lpParser.ml"
     in
    _menhir_goto_modifier _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv246)

and _menhir_run148 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.STRINGLIT _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv241 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_v : (
# 88 "src/parsing/lpParser.mly"
       (string)
# 6085 "src/parsing/lpParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _endpos, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.SWITCH _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv237 * _menhir_state * Lexing.position) * Lexing.position * (
# 88 "src/parsing/lpParser.mly"
       (string)
# 6096 "src/parsing/lpParser.ml"
            )) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let (_v : (
# 89 "src/parsing/lpParser.mly"
       (bool)
# 6102 "src/parsing/lpParser.ml"
            )) = _v in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv235 * _menhir_state * Lexing.position) * Lexing.position * (
# 88 "src/parsing/lpParser.mly"
       (string)
# 6109 "src/parsing/lpParser.ml"
            )) = Obj.magic _menhir_stack in
            let (_endpos_b_ : Lexing.position) = _endpos in
            let ((b : (
# 89 "src/parsing/lpParser.mly"
       (bool)
# 6115 "src/parsing/lpParser.ml"
            )) : (
# 89 "src/parsing/lpParser.mly"
       (bool)
# 6119 "src/parsing/lpParser.ml"
            )) = _v in
            ((let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos_s_, (s : (
# 88 "src/parsing/lpParser.mly"
       (string)
# 6124 "src/parsing/lpParser.ml"
            ))) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_b_ in
            let _v : 'tv_query = let _endpos = _endpos_b_ in
            let _symbolstartpos = _startpos__1_ in
            let _sloc = (_symbolstartpos, _endpos) in
            
# 230 "src/parsing/lpParser.mly"
                              ( make_pos _sloc (P_query_flag(s,b)) )
# 6134 "src/parsing/lpParser.ml"
             in
            _menhir_goto_query _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv236)) : 'freshtv238)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv239 * _menhir_state * Lexing.position) * Lexing.position * (
# 88 "src/parsing/lpParser.mly"
       (string)
# 6144 "src/parsing/lpParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, _), _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv240)) : 'freshtv242)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv243 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv244)

and _menhir_goto_command : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 6159 "src/parsing/lpParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv233) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 6168 "src/parsing/lpParser.ml"
    )) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv231) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((_1 : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 6176 "src/parsing/lpParser.ml"
    )) : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 6180 "src/parsing/lpParser.ml"
    )) = _v in
    (Obj.magic _1 : 'freshtv232)) : 'freshtv234)

and _menhir_run152 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.DEBUG_FLAGS _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv227 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_v : (
# 85 "src/parsing/lpParser.mly"
       (bool * string)
# 6197 "src/parsing/lpParser.ml"
        )) = _v in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv225 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        let (_endpos_fl_ : Lexing.position) = _endpos in
        let ((fl : (
# 85 "src/parsing/lpParser.mly"
       (bool * string)
# 6206 "src/parsing/lpParser.ml"
        )) : (
# 85 "src/parsing/lpParser.mly"
       (bool * string)
# 6210 "src/parsing/lpParser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_fl_ in
        let _v : 'tv_query = let _endpos = _endpos_fl_ in
        let _symbolstartpos = _startpos__1_ in
        let _sloc = (_symbolstartpos, _endpos) in
        
# 229 "src/parsing/lpParser.mly"
    ( let (b, s) = fl in make_pos _sloc (P_query_debug(b, s)) )
# 6221 "src/parsing/lpParser.ml"
         in
        _menhir_goto_query _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv226)) : 'freshtv228)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv229 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv230)

and _menhir_run154 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv223) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_modifier = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 195 "src/parsing/lpParser.mly"
             ( make_pos _sloc (P_prop Term.Const) )
# 6248 "src/parsing/lpParser.ml"
     in
    _menhir_goto_modifier _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv224)

and _menhir_run155 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.BACKQUOTE ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ID_EXPL _v ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState155 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.INT _v ->
        _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState155 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LAMBDA ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.LET ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_CU_BRACKET ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.L_PAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PI ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.QID _v ->
        _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState155 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.TYPE_TERM ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState155 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState155 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_META _v ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState155 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UID_PAT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState155 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.WILD ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState155 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState155

and _menhir_run157 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv221) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_modifier = let _endpos = _endpos__1_ in
    let _symbolstartpos = _startpos__1_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 194 "src/parsing/lpParser.mly"
                ( make_pos _sloc (P_prop Term.Commu) )
# 6307 "src/parsing/lpParser.ml"
     in
    _menhir_goto_modifier _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv222)

and _menhir_run8 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 115 "src/parsing/lpParser.mly"
       (string)
# 6314 "src/parsing/lpParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce37 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run10 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 118 "src/parsing/lpParser.mly"
       (Path.t)
# 6324 "src/parsing/lpParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce36 _menhir_env (Obj.magic _menhir_stack) _endpos _menhir_s _v _startpos

and _menhir_run142 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 84 "src/parsing/lpParser.mly"
       (Pratter.associativity)
# 6333 "src/parsing/lpParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv219) = Obj.magic _menhir_stack in
    let (_endpos_x_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((x : (
# 84 "src/parsing/lpParser.mly"
       (Pratter.associativity)
# 6344 "src/parsing/lpParser.ml"
    )) : (
# 84 "src/parsing/lpParser.mly"
       (Pratter.associativity)
# 6348 "src/parsing/lpParser.ml"
    )) = _v in
    let (_startpos_x_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : 'tv_option_ASSOC_ = 
# 116 "<standard.mly>"
    ( Some x )
# 6356 "src/parsing/lpParser.ml"
     in
    _menhir_goto_option_ASSOC_ _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv220)

and _menhir_run163 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv217) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_assert_kw = 
# 213 "src/parsing/lpParser.mly"
              ( true )
# 6373 "src/parsing/lpParser.ml"
     in
    _menhir_goto_assert_kw _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv218)

and _menhir_run164 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv215) = Obj.magic _menhir_stack in
    let (_endpos__1_ : Lexing.position) = _endpos in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_startpos__1_ : Lexing.position) = _startpos in
    ((let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : 'tv_assert_kw = 
# 212 "src/parsing/lpParser.mly"
           ( false )
# 6390 "src/parsing/lpParser.ml"
     in
    _menhir_goto_assert_kw _menhir_env _menhir_stack _endpos _menhir_s _v _startpos) : 'freshtv216)

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState277 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv35) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv36)
    | MenhirState274 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv37 * _menhir_state * 'tv_inductive)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv38)
    | MenhirState269 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv39 * Lexing.position * _menhir_state * 'tv_constructor) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv40)
    | MenhirState264 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv41 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv42)
    | MenhirState262 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv43 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv44)
    | MenhirState261 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv45 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) * Lexing.position * 'tv_option_VBAR_) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _, _menhir_s, _, _), _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv46)
    | MenhirState257 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv47 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv48)
    | MenhirState255 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv49 * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv50)
    | MenhirState254 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv51 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv52)
    | MenhirState250 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv53 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv54)
    | MenhirState247 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv55 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv56)
    | MenhirState236 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv57 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv58)
    | MenhirState234 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv59 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv60)
    | MenhirState232 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv61 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv62)
    | MenhirState230 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv63 * Lexing.position * _menhir_state * 'tv_assert_kw * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv64)
    | MenhirState227 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv65 * _menhir_state * 'tv_tactic) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv66)
    | MenhirState223 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv67 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv68)
    | MenhirState221 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv69 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv70)
    | MenhirState216 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv71 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv72)
    | MenhirState214 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv73 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv74)
    | MenhirState212 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv75 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv76)
    | MenhirState209 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv77 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv78)
    | MenhirState206 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv79 * Lexing.position * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_option_ASSOC_ * Lexing.position) * 'tv_option_delimited_L_SQ_BRACKET_rw_patt_R_SQ_BRACKET__) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv80)
    | MenhirState202 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv81 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv82)
    | MenhirState200 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv83 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv84)
    | MenhirState197 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv85 * Lexing.position) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv86)
    | MenhirState195 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv87 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv88)
    | MenhirState191 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv89 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv90)
    | MenhirState188 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv91 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv92)
    | MenhirState187 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv93) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv94)
    | MenhirState185 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv95 * Lexing.position * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv96)
    | MenhirState183 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv97 * Lexing.position * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv98)
    | MenhirState177 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv99 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv100)
    | MenhirState176 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv101 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv102)
    | MenhirState175 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv103 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv104)
    | MenhirState174 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv105 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv106)
    | MenhirState173 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv107 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv108)
    | MenhirState172 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv109 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv110)
    | MenhirState171 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv111 * Lexing.position * _menhir_state * 'tv_list_modifier_ * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv112)
    | MenhirState169 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv113 * Lexing.position * _menhir_state * 'tv_modifier * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv114)
    | MenhirState160 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv115 * _menhir_state * Lexing.position) * Lexing.position * (
# 88 "src/parsing/lpParser.mly"
       (string)
# 6599 "src/parsing/lpParser.ml"
        )) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s, _), _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv116)
    | MenhirState155 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv117 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv118)
    | MenhirState143 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv119 * Lexing.position) * Lexing.position * _menhir_state * 'tv_option_ASSOC_ * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv120)
    | MenhirState141 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv121 * Lexing.position) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv122)
    | MenhirState137 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv123) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv124)
    | MenhirState134 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv125 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv126)
    | MenhirState130 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv127 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv128)
    | MenhirState127 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv129 * Lexing.position * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv130)
    | MenhirState115 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv131 * _menhir_state * Lexing.position) * _menhir_state * 'tv_path) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv132)
    | MenhirState114 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv133 * _menhir_state * Lexing.position) * _menhir_state * 'tv_path) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv134)
    | MenhirState110 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv135 * _menhir_state * 'tv_path) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv136)
    | MenhirState109 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv137 * _menhir_state * Lexing.position) * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv138)
    | MenhirState107 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv139 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv140)
    | MenhirState105 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv141 * _menhir_state * 'tv_rule)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv142)
    | MenhirState100 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv143 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv144)
    | MenhirState98 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv145 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv146)
    | MenhirState95 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv147 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv148)
    | MenhirState93 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv149 * _menhir_state * 'tv_equation * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv150)
    | MenhirState89 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv151 * _menhir_state * 'tv_equation * Lexing.position))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv152)
    | MenhirState85 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv153 * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv154)
    | MenhirState76 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv155 * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv156)
    | MenhirState66 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv157 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) * Lexing.position) * Lexing.position * _menhir_state * 'tv_term * Lexing.position) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv158)
    | MenhirState64 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv159 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) * _menhir_state * 'tv_option_preceded_COLON_term__) * Lexing.position) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv160)
    | MenhirState62 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv161 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) * Lexing.position * _menhir_state * 'tv_list_params_ * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv162)
    | MenhirState60 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv163 * Lexing.position * _menhir_state * 'tv_params * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv164)
    | MenhirState54 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv165 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position)) * Lexing.position * _menhir_state * 'tv_term * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv166)
    | MenhirState44 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv167 * Lexing.position * _menhir_state * 'tv_patt_id * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv168)
    | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv169 * Lexing.position * _menhir_state * 'tv_saterm * Lexing.position) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv170)
    | MenhirState41 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv171 * Lexing.position * _menhir_state * 'tv_saterm * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv172)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv173 * _menhir_state * 'tv_nonempty_list_params_ * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv174)
    | MenhirState36 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv175 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_term_id * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv176)
    | MenhirState35 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv177 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv178)
    | MenhirState32 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv179 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv180)
    | MenhirState28 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv181 * Lexing.position * _menhir_state * 'tv_params * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv182)
    | MenhirState27 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv183 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv184)
    | MenhirState26 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv185 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv186)
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv187 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv188)
    | MenhirState24 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv189 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv190)
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv191 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_uid * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv192)
    | MenhirState22 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv193 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv194)
    | MenhirState21 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv195 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv196)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv197 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv198)
    | MenhirState19 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv199 * _menhir_state * Lexing.position) * Lexing.position * _menhir_state * 'tv_nonempty_list_param_id_)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv200)
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv201 * Lexing.position * _menhir_state * 'tv_param_id * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv202)
    | MenhirState14 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv203 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv204)
    | MenhirState11 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv205 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv206)
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv207 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv208)
    | MenhirState6 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv209 * Lexing.position * _menhir_state * (
# 116 "src/parsing/lpParser.mly"
       (Syntax.meta_ident)
# 6836 "src/parsing/lpParser.ml"
        ) * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv210)
    | MenhirState3 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv211 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv212)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv213) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv214)

and _menhir_reduce37 : _menhir_env -> 'ttv_tail * Lexing.position * _menhir_state * (
# 115 "src/parsing/lpParser.mly"
       (string)
# 6853 "src/parsing/lpParser.ml"
) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _endpos_i_, _menhir_s, (i : (
# 115 "src/parsing/lpParser.mly"
       (string)
# 6859 "src/parsing/lpParser.ml"
    )), _startpos_i_) = _menhir_stack in
    let _startpos = _startpos_i_ in
    let _endpos = _endpos_i_ in
    let _v : (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 6866 "src/parsing/lpParser.ml"
    ) = let _endpos = _endpos_i_ in
    let _symbolstartpos = _startpos_i_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 134 "src/parsing/lpParser.mly"
          ( make_pos _sloc ([], i) )
# 6873 "src/parsing/lpParser.ml"
     in
    _menhir_goto_id _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_reduce36 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 118 "src/parsing/lpParser.mly"
       (Path.t)
# 6880 "src/parsing/lpParser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos_p_ _menhir_s (p : (
# 118 "src/parsing/lpParser.mly"
       (Path.t)
# 6885 "src/parsing/lpParser.ml"
  )) _startpos_p_ ->
    let _startpos = _startpos_p_ in
    let _endpos = _endpos_p_ in
    let _v : (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 6892 "src/parsing/lpParser.ml"
    ) = let _endpos = _endpos_p_ in
    let _symbolstartpos = _startpos_p_ in
    let _sloc = (_symbolstartpos, _endpos) in
    
# 133 "src/parsing/lpParser.mly"
          ( qid_of_path _sloc p)
# 6899 "src/parsing/lpParser.ml"
     in
    _menhir_goto_id _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and command : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 6918 "src/parsing/lpParser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env = {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = Obj.magic ();
      _menhir_error = false;
    } in
    Obj.magic (let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv33) = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    ((let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.ASSERT ->
        _menhir_run164 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ASSERTNOT ->
        _menhir_run163 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ASSOC _v ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.BUILTIN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv15) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.STRINGLIT _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv11 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
            let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let (_v : (
# 88 "src/parsing/lpParser.mly"
       (string)
# 6954 "src/parsing/lpParser.ml"
            )) = _v in
            ((let _menhir_stack = (_menhir_stack, _endpos, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.ASSIGN ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv7 * _menhir_state * Lexing.position) * Lexing.position * (
# 88 "src/parsing/lpParser.mly"
       (string)
# 6965 "src/parsing/lpParser.ml"
                )) = Obj.magic _menhir_stack in
                let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                ((let _menhir_stack = (_menhir_stack, _endpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | LpLexer.QID _v ->
                    _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState160 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LpLexer.UID _v ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState160 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState160) : 'freshtv8)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv9 * _menhir_state * Lexing.position) * Lexing.position * (
# 88 "src/parsing/lpParser.mly"
       (string)
# 6987 "src/parsing/lpParser.ml"
                )) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s, _), _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv10)) : 'freshtv12)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv13 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv14)) : 'freshtv16)
    | LpLexer.COMMUTATIVE ->
        _menhir_run157 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.COMPUTE ->
        _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.CONSTANT ->
        _menhir_run154 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.DEBUG ->
        _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.EOF ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv19) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv17) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        ((let _v : (
# 123 "src/parsing/lpParser.mly"
       (Syntax.p_command)
# 7016 "src/parsing/lpParser.ml"
        ) = 
# 290 "src/parsing/lpParser.mly"
        ( raise End_of_file )
# 7020 "src/parsing/lpParser.ml"
         in
        _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v) : 'freshtv18)) : 'freshtv20)
    | LpLexer.FLAG ->
        _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.INJECTIVE ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.NOTATION ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv21) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.QID _v ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState134 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID _v ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState134 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState134) : 'freshtv22)
    | LpLexer.OPAQUE ->
        _menhir_run133 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.OPEN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv23) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.QID _v ->
            _menhir_run108 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState130 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.SEMICOLON ->
            _menhir_reduce43 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState130) : 'freshtv24)
    | LpLexer.PRINT ->
        _menhir_run127 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PRIVATE ->
        _menhir_run126 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PROOFTERM ->
        _menhir_run125 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PROTECTED ->
        _menhir_run124 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PROVER ->
        _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.PROVER_TIMEOUT ->
        _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.REQUIRE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv27) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.OPEN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv25 * _menhir_state * Lexing.position) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState107 in
            let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            ((let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LpLexer.QID _v ->
                _menhir_run108 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState109 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LpLexer.SEMICOLON ->
                _menhir_reduce43 _menhir_env (Obj.magic _menhir_stack) MenhirState109
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState109) : 'freshtv26)
        | LpLexer.QID _v ->
            _menhir_run108 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState107 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.SEMICOLON ->
            _menhir_reduce43 _menhir_env (Obj.magic _menhir_stack) MenhirState107
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState107) : 'freshtv28)
    | LpLexer.RULE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv29) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.BACKQUOTE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.ID_EXPL _v ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.INT _v ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.LAMBDA ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.LET ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.L_CU_BRACKET ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.L_PAREN ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.PI ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.QID _v ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.TYPE_TERM ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID _v ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID_META _v ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID_PAT _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.WILD ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState98 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState98) : 'freshtv30)
    | LpLexer.SEQUENTIAL ->
        _menhir_run97 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.TYPE_QUERY ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.UNIF_RULE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv31) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LpLexer.BACKQUOTE ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.ID_EXPL _v ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.INT _v ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.LAMBDA ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.LET ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.L_CU_BRACKET ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.L_PAREN ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.PI ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.QID _v ->
            _menhir_run10 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.TYPE_TERM ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID _v ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID_META _v ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.UID_PAT _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LpLexer.WILD ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState3) : 'freshtv32)
    | LpLexer.VERBOSE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LpLexer.ASSOCIATIVE ->
        _menhir_reduce66 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LpLexer.INDUCTIVE | LpLexer.L_CU_BRACKET | LpLexer.L_PAREN | LpLexer.SYMBOL | LpLexer.UID _ | LpLexer.WILD ->
        _menhir_reduce39 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0) : 'freshtv34))

and id : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 124 "src/parsing/lpParser.mly"
       (Syntax.p_qident)
# 7209 "src/parsing/lpParser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env = {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = Obj.magic ();
      _menhir_error = false;
    } in
    Obj.magic (let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv5) = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    ((let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LpLexer.QID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_menhir_s : _menhir_state) = MenhirState277 in
        let (_v : (
# 118 "src/parsing/lpParser.mly"
       (Path.t)
# 7231 "src/parsing/lpParser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        (_menhir_reduce36 _menhir_env (Obj.magic _menhir_stack) _endpos _menhir_s _v _startpos : 'freshtv2)
    | LpLexer.UID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv3) = Obj.magic _menhir_stack in
        let (_endpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let (_menhir_s : _menhir_state) = MenhirState277 in
        let (_v : (
# 115 "src/parsing/lpParser.mly"
       (string)
# 7243 "src/parsing/lpParser.ml"
        )) = _v in
        let (_startpos : Lexing.position) = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        ((let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
        _menhir_reduce37 _menhir_env (Obj.magic _menhir_stack)) : 'freshtv4)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState277) : 'freshtv6))

# 346 "src/parsing/lpParser.mly"
  

# 7256 "src/parsing/lpParser.ml"

# 269 "<standard.mly>"
  

# 7261 "src/parsing/lpParser.ml"
