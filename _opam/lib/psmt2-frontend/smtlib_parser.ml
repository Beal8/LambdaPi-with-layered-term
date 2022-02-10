
module MenhirBasics = struct
  
  exception Error
  
  let _eRR : exn =
    Error
  
  type token = 
    | VERSION
    | VERBOSITY
    | VALUES
    | UNDERSCORE
    | THEORIES
    | SYMBOL of (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 19 "src/lib/smtlib_parser.ml"
  )
    | STRINGLIT of (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 24 "src/lib/smtlib_parser.ml"
  )
    | STATUTS
    | SOURCE
    | SORTSDESCRIPTION
    | SORTS
    | SMTLIBVERSION
    | SETOPTION
    | SETLOGIC
    | SETINFO
    | SERIES
    | RP
    | RESSOURCELIMIT
    | RESETASSERTIONS
    | RESET
    | REGULAROUTPUTCHAN
    | REASONUNKNOWN
    | RANDOMSEED
    | PUSH
    | PRODUCEUNSATCORES
    | PRODUCEUNSATASSUMPTIONS
    | PRODUCEPROOFS
    | PRODUCEMODELS
    | PRODUCEASSIGNEMENT
    | PRODUCEASSERTIONS
    | PRINTSUCCESS
    | POP
    | PATTERN
    | PAR
    | NUMERAL of (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 56 "src/lib/smtlib_parser.ml"
  )
    | NOTES
    | NAMED
    | NAME
    | MATCH
    | LP
    | LICENSE
    | LET
    | LANGUAGE
    | INTERACTIVE
    | INSTANCE
    | INCREMENTAL
    | HEXADECIMAL of (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 72 "src/lib/smtlib_parser.ml"
  )
    | GLOBALDECLARATIONS
    | GETVALUE
    | GETUNSATCORE
    | GETUNSATASSUMPTIONS
    | GETPROOF
    | GETOPTION
    | GETMODEL
    | GETINFO
    | GETASSIGN
    | GETASSERT
    | FUNSDESCRIPT
    | FUNS
    | FORALL
    | EXTENSIONS
    | EXIT
    | EXISTS
    | EXCLIMATIONPT
    | ERRORBEHAV
    | EOF
    | ECHO
    | DIFFICULTY
    | DIAGNOOUTPUTCHAN
    | DEFINITIO
    | DEFINESORT
    | DEFINEFUNSREC
    | DEFINEFUNREC
    | DEFINEFUN
    | DECLARESORT
    | DECLAREFUN
    | DECLAREDATATYPES
    | DECLAREDATATYPE
    | DECLARECONST
    | DECIMAL of (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 109 "src/lib/smtlib_parser.ml"
  )
    | CHECKSATASSUMING
    | CHECKSAT
    | CHECKENTAILMENT
    | CHECKALLSAT
    | CATEGORY
    | BINARY of (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 119 "src/lib/smtlib_parser.ml"
  )
    | AXIOMS
    | AUTHORS
    | AUTHOR
    | ASSERTIONSTACKLVL
    | ASSERT
    | ASCIIWOR of (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 129 "src/lib/smtlib_parser.ml"
  )
    | AS
    | ALLSTATS
  
end

include MenhirBasics

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState380
  | MenhirState378
  | MenhirState376
  | MenhirState374
  | MenhirState369
  | MenhirState366
  | MenhirState363
  | MenhirState357
  | MenhirState355
  | MenhirState353
  | MenhirState352
  | MenhirState345
  | MenhirState341
  | MenhirState340
  | MenhirState339
  | MenhirState332
  | MenhirState330
  | MenhirState328
  | MenhirState327
  | MenhirState326
  | MenhirState323
  | MenhirState322
  | MenhirState320
  | MenhirState313
  | MenhirState306
  | MenhirState303
  | MenhirState302
  | MenhirState301
  | MenhirState300
  | MenhirState299
  | MenhirState296
  | MenhirState294
  | MenhirState293
  | MenhirState289
  | MenhirState285
  | MenhirState284
  | MenhirState279
  | MenhirState275
  | MenhirState272
  | MenhirState271
  | MenhirState268
  | MenhirState266
  | MenhirState264
  | MenhirState260
  | MenhirState257
  | MenhirState256
  | MenhirState253
  | MenhirState252
  | MenhirState250
  | MenhirState246
  | MenhirState240
  | MenhirState236
  | MenhirState233
  | MenhirState232
  | MenhirState229
  | MenhirState227
  | MenhirState225
  | MenhirState224
  | MenhirState220
  | MenhirState217
  | MenhirState216
  | MenhirState214
  | MenhirState211
  | MenhirState202
  | MenhirState197
  | MenhirState185
  | MenhirState183
  | MenhirState179
  | MenhirState175
  | MenhirState174
  | MenhirState172
  | MenhirState171
  | MenhirState168
  | MenhirState166
  | MenhirState162
  | MenhirState159
  | MenhirState156
  | MenhirState155
  | MenhirState154
  | MenhirState150
  | MenhirState147
  | MenhirState144
  | MenhirState143
  | MenhirState140
  | MenhirState139
  | MenhirState131
  | MenhirState130
  | MenhirState129
  | MenhirState128
  | MenhirState127
  | MenhirState126
  | MenhirState125
  | MenhirState123
  | MenhirState113
  | MenhirState108
  | MenhirState107
  | MenhirState106
  | MenhirState104
  | MenhirState103
  | MenhirState101
  | MenhirState99
  | MenhirState96
  | MenhirState95
  | MenhirState94
  | MenhirState93
  | MenhirState79
  | MenhirState76
  | MenhirState64
  | MenhirState59
  | MenhirState58
  | MenhirState55
  | MenhirState51
  | MenhirState8
  | MenhirState3
  | MenhirState1
  | MenhirState0

# 6 "src/lib/smtlib_parser.mly"
  
   open Smtlib_syntax

   let mk_data p c =
     let p =
       if Options.keep_loc () then Some p
       else None
     in
       {p;c;ty= Smtlib_ty.new_type Smtlib_ty.TDummy;is_quantif=false}

# 274 "src/lib/smtlib_parser.ml"

let rec _menhir_goto_nonempty_list_datatype_dec_ : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Smtlib_syntax.symbol list * Smtlib_syntax.constructor_dec list) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState293 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__9_ = _endpos in
                let ((((((((_menhir_stack, _menhir_s, _startpos__1_), _), _startpos__3_), _, (_4 : (Smtlib_syntax.sort_dec list))), _endpos__5_), _startpos__6_), _, (_7 : ((Smtlib_syntax.symbol list * Smtlib_syntax.constructor_dec list) list))), _endpos__8_) = _menhir_stack in
                let _v : (Smtlib_syntax.command) = let _endpos = _endpos__9_ in
                let _startpos = _startpos__1_ in
                
# 279 "src/lib/smtlib_parser.mly"
        ( mk_data (_startpos,_endpos) (Cmd_DeclareDataTypes (_4,_7)) )
# 304 "src/lib/smtlib_parser.ml"
                 in
                _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState320 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smtlib_syntax.symbol list * Smtlib_syntax.constructor_dec list))), _, (xs : ((Smtlib_syntax.symbol list * Smtlib_syntax.constructor_dec list) list))) = _menhir_stack in
        let _v : ((Smtlib_syntax.symbol list * Smtlib_syntax.constructor_dec list) list) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 326 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_nonempty_list_datatype_dec_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_datatype_dec : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.symbol list * Smtlib_syntax.constructor_dec list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState320 | MenhirState293 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            _menhir_run294 _menhir_env (Obj.magic _menhir_stack) MenhirState320 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (x : (Smtlib_syntax.symbol list * Smtlib_syntax.constructor_dec list))) = _menhir_stack in
            let _v : ((Smtlib_syntax.symbol list * Smtlib_syntax.constructor_dec list) list) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 349 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_nonempty_list_datatype_dec_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState320)
    | MenhirState323 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let ((((_menhir_stack, _menhir_s, _startpos__1_), _), _endpos__3_, _, (_3 : (Smtlib_syntax.symbol)), _startpos__3_), _, (_4 : (Smtlib_syntax.symbol list * Smtlib_syntax.constructor_dec list))) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__5_ in
            let _startpos = _startpos__1_ in
            
# 276 "src/lib/smtlib_parser.mly"
        ( mk_data (_startpos,_endpos) (Cmd_DeclareDataType (_3,_4)) )
# 373 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_constructor_dec_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.constructor_dec list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState299 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__9_ = _endpos in
                let ((((((((_menhir_stack, _menhir_s, _startpos__1_), _), _startpos__3_), _, (_4 : (Smtlib_syntax.symbol list))), _endpos__5_), _startpos__6_), _, (_7 : (Smtlib_syntax.constructor_dec list))), _endpos__8_) = _menhir_stack in
                let _v : (Smtlib_syntax.symbol list * Smtlib_syntax.constructor_dec list) = 
# 227 "src/lib/smtlib_parser.mly"
        ( _4,_7 )
# 411 "src/lib/smtlib_parser.ml"
                 in
                _menhir_goto_datatype_dec _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState313 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smtlib_syntax.constructor_dec))), _, (xs : (Smtlib_syntax.constructor_dec list))) = _menhir_stack in
        let _v : (Smtlib_syntax.constructor_dec list) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 433 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_nonempty_list_constructor_dec_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState294 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (_2 : (Smtlib_syntax.constructor_dec list))) = _menhir_stack in
            let _v : (Smtlib_syntax.symbol list * Smtlib_syntax.constructor_dec list) = 
# 225 "src/lib/smtlib_parser.mly"
        ( [],_2 )
# 451 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_datatype_dec _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_key_term_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.key_term list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState172 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let ((((_menhir_stack, _menhir_s, _startpos__1_), _), _, (_3 : (Smtlib_syntax.term))), _, (_4 : (Smtlib_syntax.key_term list))) = _menhir_stack in
            let _v : (Smtlib_syntax.term) = let _endpos = _endpos__5_ in
            let _startpos = _startpos__1_ in
            
# 153 "src/lib/smtlib_parser.mly"
       ( mk_data (_startpos,_endpos) (TermExclimationPt (_3, _4)) )
# 484 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState183 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smtlib_syntax.key_term))), _, (xs : (Smtlib_syntax.key_term list))) = _menhir_stack in
        let _v : (Smtlib_syntax.key_term list) = 
# 213 "<standard.mly>"
    ( x :: xs )
# 500 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_list_key_term_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_const_dec : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.symbol list * Smtlib_syntax.sort) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RP ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__5_ = _endpos in
        let ((((_menhir_stack, _menhir_s, _startpos__1_), _), _endpos__3_, _, (_3 : (Smtlib_syntax.symbol)), _startpos__3_), _, (_4 : (Smtlib_syntax.symbol list * Smtlib_syntax.sort))) = _menhir_stack in
        let _v : (Smtlib_syntax.command) = let _endpos = _endpos__5_ in
        let _startpos = _startpos__1_ in
        
# 274 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_DeclareConst (_3,_4)) )
# 525 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_fun_dec : _menhir_env -> 'ttv_tail -> (Smtlib_syntax.symbol list * Smtlib_syntax.sort list * Smtlib_syntax.sort) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RP ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__5_ = _endpos in
        let ((((_menhir_stack, _menhir_s, _startpos__1_), _), _endpos__3_, _, (_3 : (Smtlib_syntax.symbol)), _startpos__3_), (_4 : (Smtlib_syntax.symbol list * Smtlib_syntax.sort list * Smtlib_syntax.sort))) = _menhir_stack in
        let _v : (Smtlib_syntax.command) = let _endpos = _endpos__5_ in
        let _startpos = _startpos__1_ in
        
# 281 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_DeclareFun(_3, _4)) )
# 554 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_fun_def : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.symbol * Smtlib_syntax.symbol list *
  Smtlib_syntax.sorted_var list * Smtlib_syntax.sort) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState225 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (_2 : (Smtlib_syntax.symbol * Smtlib_syntax.symbol list *
  Smtlib_syntax.sorted_var list * Smtlib_syntax.sort))) = _menhir_stack in
            let _v : (Smtlib_syntax.symbol * Smtlib_syntax.symbol list *
  Smtlib_syntax.sorted_var list * Smtlib_syntax.sort) = 
# 252 "src/lib/smtlib_parser.mly"
                    ( _2 )
# 586 "src/lib/smtlib_parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LP ->
                _menhir_run225 _menhir_env (Obj.magic _menhir_stack) MenhirState250 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RP ->
                _menhir_reduce109 _menhir_env (Obj.magic _menhir_stack) MenhirState250
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState250)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState252 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState253 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | BINARY _v ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState253 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DECIMAL _v ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState253 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HEXADECIMAL _v ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState253 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState253 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUMERAL _v ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState253 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STRINGLIT _v ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState253 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState253 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState253)
    | MenhirState256 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | BINARY _v ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DECIMAL _v ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HEXADECIMAL _v ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState257 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUMERAL _v ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STRINGLIT _v ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState257 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState257)
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_sorted_var_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.sorted_var list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState159 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smtlib_syntax.sorted_var))), _, (xs : (Smtlib_syntax.sorted_var list))) = _menhir_stack in
        let _v : (Smtlib_syntax.sorted_var list) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 671 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_nonempty_list_sorted_var_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState154 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState162 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | BINARY _v ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState162 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DECIMAL _v ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState162 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | HEXADECIMAL _v ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState162 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUMERAL _v ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState162 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRINGLIT _v ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState162 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState162 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState162)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState168 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | BINARY _v ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState168 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DECIMAL _v ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState168 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | HEXADECIMAL _v ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState168 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUMERAL _v ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState168 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRINGLIT _v ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState168 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState168 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState168)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_sort_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.sort list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smtlib_syntax.sort))), _, (xs : (Smtlib_syntax.sort list))) = _menhir_stack in
        let _v : (Smtlib_syntax.sort list) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 764 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_nonempty_list_sort_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState130 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Smtlib_syntax.identifier)), _startpos__2_), _, (_3 : (Smtlib_syntax.sort list))) = _menhir_stack in
            let _v : (Smtlib_syntax.sort) = let _endpos = _endpos__4_ in
            let _startpos = _startpos__1_ in
            
# 97 "src/lib/smtlib_parser.mly"
      ( mk_data (_startpos,_endpos) (SortIdMulti(_2, _3)) )
# 784 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_sort _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_sexpr_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.sexpr list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smtlib_syntax.sexpr))), _, (xs : (Smtlib_syntax.sexpr list))) = _menhir_stack in
        let _v : (Smtlib_syntax.sexpr list) = 
# 213 "<standard.mly>"
    ( x :: xs )
# 807 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_list_sexpr_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (_2 : (Smtlib_syntax.sexpr list))) = _menhir_stack in
            let _v : (Smtlib_syntax.sexpr) = let _endpos = _endpos__3_ in
            let _startpos = _startpos__1_ in
            
# 114 "src/lib/smtlib_parser.mly"
                        ( mk_data (_startpos,_endpos) (SexprInParen _2) )
# 827 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_sexpr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState58 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, (_2 : (Smtlib_syntax.sexpr list))) = _menhir_stack in
            let _endpos = _endpos__3_ in
            let _v : (Smtlib_syntax.attribute_value_aux Smtlib_syntax.data) = let _endpos = _endpos__3_ in
            let _startpos = _startpos__1_ in
            
# 103 "src/lib/smtlib_parser.mly"
                        ( mk_data (_startpos,_endpos) (AttributeValSexpr _2) )
# 854 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_attribute_value _menhir_env _menhir_stack _endpos _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_assert_dec : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.symbol list * Smtlib_syntax.term) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState352 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _), _, (_3 : (Smtlib_syntax.symbol list * Smtlib_syntax.term))) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__4_ in
            let _startpos = _startpos__1_ in
            
# 270 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_CheckEntailment _3) )
# 887 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState366 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _), _, (_3 : (Smtlib_syntax.symbol list * Smtlib_syntax.term))) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__4_ in
            let _startpos = _startpos__1_ in
            
# 264 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_Assert (_3)) )
# 913 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_term_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.term list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState175 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smtlib_syntax.term))), _, (xs : (Smtlib_syntax.term list))) = _menhir_stack in
        let _v : (Smtlib_syntax.term list) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 936 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_nonempty_list_term_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState174 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _startpos__2_), _, (_3 : (Smtlib_syntax.term list))) = _menhir_stack in
            let _v : (Smtlib_syntax.key_term) = let _endpos = _endpos__4_ in
            let _startpos = _startpos__1_ in
            
# 213 "src/lib/smtlib_parser.mly"
      ( mk_data (_startpos,_endpos) (Pattern _3) )
# 956 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_key_term _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState185 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Smtlib_syntax.qualidentifier)), _startpos__2_), _, (_3 : (Smtlib_syntax.term list))) = _menhir_stack in
            let _v : (Smtlib_syntax.term) = let _endpos = _endpos__4_ in
            let _startpos = _startpos__1_ in
            
# 141 "src/lib/smtlib_parser.mly"
       ( mk_data (_startpos,_endpos) (TermQualIdTerm (_2, _3)) )
# 982 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState93 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__6_ = _endpos in
                let (((((_menhir_stack, _menhir_s, _startpos__1_), _), _startpos__3_), _, (_4 : (Smtlib_syntax.term list))), _endpos__5_) = _menhir_stack in
                let _v : (Smtlib_syntax.command) = let _endpos = _endpos__6_ in
                let _startpos = _startpos__1_ in
                
# 313 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_GetValue _4) )
# 1015 "src/lib/smtlib_parser.ml"
                 in
                _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState246 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__9_ = _endpos in
                let ((((((((_menhir_stack, _menhir_s, _startpos__1_), _), _startpos__3_), _, (_4 : ((Smtlib_syntax.symbol * Smtlib_syntax.symbol list *
   Smtlib_syntax.sorted_var list * Smtlib_syntax.sort)
  list))), _endpos__5_), _startpos__6_), _, (_7 : (Smtlib_syntax.term list))), _endpos__8_) = _menhir_stack in
                let _v : (Smtlib_syntax.command) = let _endpos = _endpos__9_ in
                let _startpos = _startpos__1_ in
                
# 289 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_DefineFunsRec (_4,_7)) )
# 1056 "src/lib/smtlib_parser.ml"
                 in
                _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_varbinding_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.varbinding list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState147 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smtlib_syntax.varbinding))), _, (xs : (Smtlib_syntax.varbinding list))) = _menhir_stack in
        let _v : (Smtlib_syntax.varbinding list) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 1085 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_nonempty_list_varbinding_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | BINARY _v ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DECIMAL _v ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | HEXADECIMAL _v ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUMERAL _v ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRINGLIT _v ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState150 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState150)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_match_case_ : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Smtlib_syntax.pattern * Smtlib_syntax.term) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState103 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__7_ = _endpos in
                let ((((((_menhir_stack, _menhir_s, _startpos__1_), _), _, (_3 : (Smtlib_syntax.term))), _startpos__4_), _, (_5 : ((Smtlib_syntax.pattern * Smtlib_syntax.term) list))), _endpos__6_) = _menhir_stack in
                let _v : (Smtlib_syntax.term) = let _endpos = _endpos__7_ in
                let _startpos = _startpos__1_ in
                
# 151 "src/lib/smtlib_parser.mly"
       ( mk_data (_startpos,_endpos) (TermMatch (_3, _5)) )
# 1157 "src/lib/smtlib_parser.ml"
                 in
                _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState123 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smtlib_syntax.pattern * Smtlib_syntax.term))), _, (xs : ((Smtlib_syntax.pattern * Smtlib_syntax.term) list))) = _menhir_stack in
        let _v : ((Smtlib_syntax.pattern * Smtlib_syntax.term) list) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 1179 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_nonempty_list_match_case_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run104 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState104 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LP ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState104 in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState106 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState106 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState106)
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState104 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UNDERSCORE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_s = MenhirState104 in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__1_ = _endpos in
        let _startpos__1_ = _startpos in
        let _v : (Smtlib_syntax.pattern_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 130 "src/lib/smtlib_parser.mly"
                 ( mk_data (_startpos,_endpos) MatchUnderscore )
# 1225 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState104

and _menhir_goto_list_selector_dec_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.selector_dec list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState306 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smtlib_syntax.selector_dec))), _, (xs : (Smtlib_syntax.selector_dec list))) = _menhir_stack in
        let _v : (Smtlib_syntax.selector_dec list) = 
# 213 "<standard.mly>"
    ( x :: xs )
# 1244 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_list_selector_dec_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState301 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Smtlib_syntax.symbol)), _startpos__2_), _, (_3 : (Smtlib_syntax.selector_dec list))) = _menhir_stack in
            let _v : (Smtlib_syntax.constructor_dec) = 
# 221 "src/lib/smtlib_parser.mly"
                                      ( _2,_3 )
# 1262 "src/lib/smtlib_parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LP ->
                _menhir_run300 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (x : (Smtlib_syntax.constructor_dec))) = _menhir_stack in
                let _v : (Smtlib_syntax.constructor_dec list) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 1277 "src/lib/smtlib_parser.ml"
                 in
                _menhir_goto_nonempty_list_constructor_dec_ _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState313)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_sort_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.sort list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState272 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smtlib_syntax.sort))), _, (xs : (Smtlib_syntax.sort list))) = _menhir_stack in
        let _v : (Smtlib_syntax.sort list) = 
# 213 "<standard.mly>"
    ( x :: xs )
# 1304 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_list_sort_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState271 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState275 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState275 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState275)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState266 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState279 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState279 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState279 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState279)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_sorted_var_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.sorted_var list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState233 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smtlib_syntax.sorted_var))), _, (xs : (Smtlib_syntax.sorted_var list))) = _menhir_stack in
        let _v : (Smtlib_syntax.sorted_var list) = 
# 213 "<standard.mly>"
    ( x :: xs )
# 1377 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_list_sorted_var_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState232 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState236 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState236 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState236 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState236)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState227 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState240 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState240 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState240 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState240)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce111 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Smtlib_syntax.key_term list) = 
# 211 "<standard.mly>"
    ( [] )
# 1444 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_list_key_term_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run173 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LP ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState174 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | BINARY _v ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState174 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DECIMAL _v ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState174 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HEXADECIMAL _v ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState174 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState174 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUMERAL _v ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState174 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STRINGLIT _v ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState174 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState174 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState174)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run179 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState179 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState179 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState179

and _menhir_goto_sort : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.sort) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState131 | MenhirState130 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState131 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (x : (Smtlib_syntax.sort))) = _menhir_stack in
            let _v : (Smtlib_syntax.sort list) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 1524 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_nonempty_list_sort_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState131)
    | MenhirState128 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let ((((_menhir_stack, _menhir_s, _startpos__1_), _), _endpos__3_, _, (_3 : (Smtlib_syntax.identifier)), _startpos__3_), _, (_4 : (Smtlib_syntax.sort))) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__5_ in
            let _v : (Smtlib_syntax.qualidentifier) = let _endpos = _endpos__5_ in
            let _startpos = _startpos__1_ in
            
# 126 "src/lib/smtlib_parser.mly"
      ( mk_data (_startpos,_endpos) (QualIdentifierAs(_3, _4)) )
# 1550 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_qualidentifier _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Smtlib_syntax.symbol)), _startpos__2_), _, (_3 : (Smtlib_syntax.sort))) = _menhir_stack in
            let _v : (Smtlib_syntax.sorted_var) = 
# 121 "src/lib/smtlib_parser.mly"
                        ( _2,_3 )
# 1574 "src/lib/smtlib_parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            (match _menhir_s with
            | MenhirState166 | MenhirState159 | MenhirState154 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LP ->
                    _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState159 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | RP ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, (x : (Smtlib_syntax.sorted_var))) = _menhir_stack in
                    let _v : (Smtlib_syntax.sorted_var list) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 1591 "src/lib/smtlib_parser.ml"
                     in
                    _menhir_goto_nonempty_list_sorted_var_ _menhir_env _menhir_stack _menhir_s _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState159)
            | MenhirState227 | MenhirState233 | MenhirState232 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LP ->
                    _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState233 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | RP ->
                    _menhir_reduce121 _menhir_env (Obj.magic _menhir_stack) MenhirState233
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState233)
            | _ ->
                _menhir_fail ())
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState220 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__8_ = _endpos in
            let (((((((_menhir_stack, _menhir_s, _startpos__1_), _), _endpos__3_, _, (_3 : (Smtlib_syntax.symbol)), _startpos__3_), _startpos__4_), _, (_5 : (Smtlib_syntax.symbol list))), _endpos__6_), _, (_7 : (Smtlib_syntax.sort))) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__8_ in
            let _startpos = _startpos__1_ in
            
# 291 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_DefineSort(_3, _5, _7)) )
# 1636 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState236 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__11_ = _endpos in
            let ((((((((((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.symbol)), _startpos__1_), _startpos__2_), _), _startpos__4_), _, (_5 : (Smtlib_syntax.symbol list))), _endpos__6_), _startpos__7_), _, (_8 : (Smtlib_syntax.sorted_var list))), _endpos__9_), _, (_10 : (Smtlib_syntax.sort))) = _menhir_stack in
            let _v : (Smtlib_syntax.symbol * Smtlib_syntax.symbol list *
  Smtlib_syntax.sorted_var list * Smtlib_syntax.sort) = 
# 249 "src/lib/smtlib_parser.mly"
        ( _1,_5,_8,_10 )
# 1661 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_fun_def _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState240 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.symbol)), _startpos__1_), _startpos__2_), _, (_3 : (Smtlib_syntax.sorted_var list))), _endpos__4_), _, (_5 : (Smtlib_syntax.sort))) = _menhir_stack in
        let _v : (Smtlib_syntax.symbol * Smtlib_syntax.symbol list *
  Smtlib_syntax.sorted_var list * Smtlib_syntax.sort) = 
# 247 "src/lib/smtlib_parser.mly"
        ( _1,[],_3,_5 )
# 1678 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_fun_def _menhir_env _menhir_stack _menhir_s _v
    | MenhirState266 | MenhirState272 | MenhirState271 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState272 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState272 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState272 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RP ->
            _menhir_reduce119 _menhir_env (Obj.magic _menhir_stack) MenhirState272
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState272)
    | MenhirState275 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__10_ = _endpos in
            let (((((((((_menhir_stack, _startpos__1_), _), _startpos__3_), _, (_4 : (Smtlib_syntax.symbol list))), _endpos__5_), _startpos__6_), _, (_7 : (Smtlib_syntax.sort list))), _endpos__8_), _, (_9 : (Smtlib_syntax.sort))) = _menhir_stack in
            let _v : (Smtlib_syntax.symbol list * Smtlib_syntax.sort list * Smtlib_syntax.sort) = 
# 243 "src/lib/smtlib_parser.mly"
        ( (_4,_7,_9) )
# 1713 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_fun_dec _menhir_env _menhir_stack _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState279 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _startpos__1_), _, (_2 : (Smtlib_syntax.sort list))), _endpos__3_), _, (_4 : (Smtlib_syntax.sort))) = _menhir_stack in
        let _v : (Smtlib_syntax.symbol list * Smtlib_syntax.sort list * Smtlib_syntax.sort) = 
# 241 "src/lib/smtlib_parser.mly"
        ( [],_2,_4 )
# 1729 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_fun_dec _menhir_env _menhir_stack _v
    | MenhirState303 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Smtlib_syntax.symbol)), _startpos__2_), _, (_3 : (Smtlib_syntax.sort))) = _menhir_stack in
            let _v : (Smtlib_syntax.selector_dec) = 
# 218 "src/lib/smtlib_parser.mly"
                        ( (_2,_3) )
# 1747 "src/lib/smtlib_parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LP ->
                _menhir_run302 _menhir_env (Obj.magic _menhir_stack) MenhirState306 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RP ->
                _menhir_reduce115 _menhir_env (Obj.magic _menhir_stack) MenhirState306
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState306)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState332 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__7_ = _endpos in
            let ((((((_menhir_stack, _menhir_s, _startpos__1_), _), _startpos__3_), _, (_4 : (Smtlib_syntax.symbol list))), _endpos__5_), _, (_6 : (Smtlib_syntax.sort))) = _menhir_stack in
            let _v : (Smtlib_syntax.symbol list * Smtlib_syntax.sort) = 
# 237 "src/lib/smtlib_parser.mly"
        ( _4,_6 )
# 1783 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_const_dec _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState327 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (_1 : (Smtlib_syntax.sort))) = _menhir_stack in
        let _v : (Smtlib_syntax.symbol list * Smtlib_syntax.sort) = 
# 235 "src/lib/smtlib_parser.mly"
        ( [],_1 )
# 1799 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_const_dec _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_qualidentifier : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (Smtlib_syntax.qualidentifier) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState378 | MenhirState380 | MenhirState376 | MenhirState369 | MenhirState366 | MenhirState352 | MenhirState357 | MenhirState257 | MenhirState253 | MenhirState246 | MenhirState93 | MenhirState185 | MenhirState171 | MenhirState174 | MenhirState175 | MenhirState168 | MenhirState162 | MenhirState150 | MenhirState144 | MenhirState140 | MenhirState101 | MenhirState113 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.qualidentifier)), _startpos__1_) = _menhir_stack in
        let _v : (Smtlib_syntax.term) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 139 "src/lib/smtlib_parser.mly"
                     ( mk_data (_startpos,_endpos) (TermQualIdentifier _1) )
# 1818 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v
    | MenhirState353 | MenhirState94 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | BINARY _v ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DECIMAL _v ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HEXADECIMAL _v ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUMERAL _v ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STRINGLIT _v ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState185 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState185)
    | _ ->
        _menhir_fail ()

and _menhir_run300 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState300 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState300 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState300

and _menhir_goto_attribute : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (Smtlib_syntax.attribute) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.attribute)), _startpos__1_) = _menhir_stack in
        let _v : (Smtlib_syntax.option_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 194 "src/lib/smtlib_parser.mly"
                (mk_data (_startpos,_endpos) (Option_attribute _1) )
# 1877 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_src_lib_smtlib_parser_option _menhir_env _menhir_stack _menhir_s _v
    | MenhirState79 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _), _endpos__3_, _, (_3 : (Smtlib_syntax.attribute)), _startpos__3_) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__4_ in
            let _startpos = _startpos__1_ in
            
# 323 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_SetInfo _3) )
# 1897 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce117 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Smtlib_syntax.sexpr list) = 
# 211 "<standard.mly>"
    ( [] )
# 1914 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_list_sexpr_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run59 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | AXIOMS ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | BINARY _v ->
        _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CATEGORY ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DECIMAL _v ->
        _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DEFINITIO ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXTENSIONS ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FUNS ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FUNSDESCRIPT ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | HEXADECIMAL _v ->
        _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LANGUAGE ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LICENSE ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LP ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOTES ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUMERAL _v ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SMTLIBVERSION ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SORTS ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SORTSDESCRIPTION ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SOURCE ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STATUTS ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRINGLIT _v ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | THEORIES ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VALUES ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState59 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | RP ->
        _menhir_reduce117 _menhir_env (Obj.magic _menhir_stack) MenhirState59
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState59

and _menhir_goto_nonempty_list_index_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.index list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState96 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let ((((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, _startpos__2_), _endpos__3_, _, (_3 : (Smtlib_syntax.symbol)), _startpos__3_), _, (_4 : (Smtlib_syntax.index list))) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__5_ in
            let _v : (Smtlib_syntax.identifier) = let _endpos = _endpos__5_ in
            let _startpos = _startpos__1_ in
            
# 84 "src/lib/smtlib_parser.mly"
      ( mk_data (_startpos,_endpos) (IdUnderscoreSymNum(_3, _4)) )
# 2002 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_identifier _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_x_, _menhir_s, (x : (Smtlib_syntax.index))), _, (xs : (Smtlib_syntax.index list))) = _menhir_stack in
        let _v : (Smtlib_syntax.index list) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 2018 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_nonempty_list_index_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_src_lib_smtlib_parser_option : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.option_aux Smtlib_syntax.data) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RP ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__4_ = _endpos in
        let (((_menhir_stack, _menhir_s, _startpos__1_), _), _, (_3 : (Smtlib_syntax.option_aux Smtlib_syntax.data))) = _menhir_stack in
        let _v : (Smtlib_syntax.command) = let _endpos = _endpos__4_ in
        let _startpos = _startpos__1_ in
        
# 328 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_SetOption _3) )
# 2043 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_key_info : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (Smtlib_syntax.key_info_aux Smtlib_syntax.data) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState79 | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState55 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | BINARY _v ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState55 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DECIMAL _v ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState55 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HEXADECIMAL _v ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState55 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState55 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | AXIOMS ->
                _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | BINARY _v ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | CATEGORY ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DECIMAL _v ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DEFINITIO ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | EXTENSIONS ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FUNS ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | FUNSDESCRIPT ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | HEXADECIMAL _v ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LANGUAGE ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LICENSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NOTES ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUMERAL _v ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SMTLIBVERSION ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SORTS ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SORTSDESCRIPTION ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SOURCE ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STATUTS ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRINGLIT _v ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | THEORIES ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | VALUES ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState58 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RP ->
                _menhir_reduce117 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState58)
        | NUMERAL _v ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState55 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STRINGLIT _v ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState55 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState55 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.key_info_aux Smtlib_syntax.data)), _startpos__1_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__1_ in
            let _v : (Smtlib_syntax.attribute) = let _endpos = _endpos__1_ in
            let _startpos = _startpos__1_ in
            
# 106 "src/lib/smtlib_parser.mly"
               ( mk_data (_startpos,_endpos) (AttributeKey _1) )
# 2148 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_attribute _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState55)
    | MenhirState202 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _), _endpos__3_, _, (_3 : (Smtlib_syntax.key_info_aux Smtlib_syntax.data)), _startpos__3_) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__4_ in
            let _startpos = _startpos__1_ in
            
# 301 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_GetInfo _3) )
# 2172 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_fun_defs_ : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Smtlib_syntax.symbol * Smtlib_syntax.symbol list *
   Smtlib_syntax.sorted_var list * Smtlib_syntax.sort)
  list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState224 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ASCIIWOR _v ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState246 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | BINARY _v ->
                    _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState246 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | DECIMAL _v ->
                    _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState246 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | HEXADECIMAL _v ->
                    _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState246 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LP ->
                    _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState246 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | NUMERAL _v ->
                    _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState246 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | STRINGLIT _v ->
                    _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState246 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | SYMBOL _v ->
                    _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState246 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState246)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState250 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smtlib_syntax.symbol * Smtlib_syntax.symbol list *
  Smtlib_syntax.sorted_var list * Smtlib_syntax.sort))), _, (xs : ((Smtlib_syntax.symbol * Smtlib_syntax.symbol list *
   Smtlib_syntax.sorted_var list * Smtlib_syntax.sort)
  list))) = _menhir_stack in
        let _v : ((Smtlib_syntax.symbol * Smtlib_syntax.symbol list *
   Smtlib_syntax.sorted_var list * Smtlib_syntax.sort)
  list) = 
# 213 "<standard.mly>"
    ( x :: xs )
# 2253 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_list_fun_defs_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_prop_literal_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.prop_literal list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState345 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smtlib_syntax.prop_literal_aux Smtlib_syntax.data))), _, (xs : (Smtlib_syntax.prop_literal list))) = _menhir_stack in
        let _v : (Smtlib_syntax.prop_literal list) = 
# 213 "<standard.mly>"
    ( x :: xs )
# 2270 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_list_prop_literal_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState339 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__6_ = _endpos in
                let (((((_menhir_stack, _menhir_s, _startpos__1_), _), _startpos__3_), _, (_4 : (Smtlib_syntax.prop_literal list))), _endpos__5_) = _menhir_stack in
                let _v : (Smtlib_syntax.command) = let _endpos = _endpos__6_ in
                let _startpos = _startpos__1_ in
                
# 268 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_CheckSatAssum _4) )
# 2297 "src/lib/smtlib_parser.ml"
                 in
                _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_symbol_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.symbol list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState217 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_x_, _menhir_s, (x : (Smtlib_syntax.symbol)), _startpos_x_), _, (xs : (Smtlib_syntax.symbol list))) = _menhir_stack in
        let _v : (Smtlib_syntax.symbol list) = 
# 213 "<standard.mly>"
    ( x :: xs )
# 2326 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_list_symbol_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState216 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState220 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState220 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState220 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState220)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState363 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _), _, (_3 : (Smtlib_syntax.symbol list))) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__4_ in
            let _startpos = _startpos__1_ in
            
# 272 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_CheckAllSat _3) )
# 2374 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run143 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState143 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState143 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState143

and _menhir_goto_term : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.term) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState101 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LP ->
                _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState103 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState103)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState113 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _, (_2 : (Smtlib_syntax.pattern_aux Smtlib_syntax.data))), _, (_3 : (Smtlib_syntax.term))) = _menhir_stack in
            let _v : (Smtlib_syntax.pattern * Smtlib_syntax.term) = 
# 135 "src/lib/smtlib_parser.mly"
                         ( (_2,_3) )
# 2444 "src/lib/smtlib_parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LP ->
                _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (x : (Smtlib_syntax.pattern * Smtlib_syntax.term))) = _menhir_stack in
                let _v : ((Smtlib_syntax.pattern * Smtlib_syntax.term) list) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 2459 "src/lib/smtlib_parser.ml"
                 in
                _menhir_goto_nonempty_list_match_case_ _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState123)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState140 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__6_ = _endpos in
            let (((((_menhir_stack, _menhir_s, _startpos__1_), _), _startpos__3_), _endpos__4_, _), _, (_5 : (Smtlib_syntax.term))) = _menhir_stack in
            let _v : (Smtlib_syntax.term) = 
# 145 "src/lib/smtlib_parser.mly"
       ( _5 )
# 2487 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState144 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Smtlib_syntax.symbol)), _startpos__2_), _, (_3 : (Smtlib_syntax.term))) = _menhir_stack in
            let _v : (Smtlib_syntax.varbinding) = 
# 118 "src/lib/smtlib_parser.mly"
                        ( _2,_3 )
# 2511 "src/lib/smtlib_parser.ml"
             in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LP ->
                _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, (x : (Smtlib_syntax.varbinding))) = _menhir_stack in
                let _v : (Smtlib_syntax.varbinding list) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 2526 "src/lib/smtlib_parser.ml"
                 in
                _menhir_goto_nonempty_list_varbinding_ _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState147)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__7_ = _endpos in
            let ((((((_menhir_stack, _menhir_s, _startpos__1_), _), _startpos__3_), _, (_4 : (Smtlib_syntax.varbinding list))), _endpos__5_), _, (_6 : (Smtlib_syntax.term))) = _menhir_stack in
            let _v : (Smtlib_syntax.term) = let _endpos = _endpos__7_ in
            let _startpos = _startpos__1_ in
            
# 143 "src/lib/smtlib_parser.mly"
       ( mk_data (_startpos,_endpos) (TermLetTerm (_4, _6)) )
# 2556 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState162 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__7_ = _endpos in
            let ((((((_menhir_stack, _menhir_s, _startpos__1_), _), _startpos__3_), _, (_4 : (Smtlib_syntax.sorted_var list))), _endpos__5_), _, (_6 : (Smtlib_syntax.term))) = _menhir_stack in
            let _v : (Smtlib_syntax.term) = let _endpos = _endpos__7_ in
            let _startpos = _startpos__1_ in
            
# 147 "src/lib/smtlib_parser.mly"
       ( mk_data (_startpos,_endpos) (TermForAllTerm (_4, _6)) )
# 2582 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState168 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__7_ = _endpos in
            let ((((((_menhir_stack, _menhir_s, _startpos__1_), _), _startpos__3_), _, (_4 : (Smtlib_syntax.sorted_var list))), _endpos__5_), _, (_6 : (Smtlib_syntax.term))) = _menhir_stack in
            let _v : (Smtlib_syntax.term) = let _endpos = _endpos__7_ in
            let _startpos = _startpos__1_ in
            
# 149 "src/lib/smtlib_parser.mly"
       ( mk_data (_startpos,_endpos) (TermExistsTerm (_4, _6)) )
# 2608 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState171 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | NAMED ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PATTERN ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RP ->
            _menhir_reduce111 _menhir_env (Obj.magic _menhir_stack) MenhirState172
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState172)
    | MenhirState246 | MenhirState93 | MenhirState185 | MenhirState175 | MenhirState174 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | BINARY _v ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DECIMAL _v ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HEXADECIMAL _v ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState175 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUMERAL _v ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STRINGLIT _v ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState175 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (x : (Smtlib_syntax.term))) = _menhir_stack in
            let _v : (Smtlib_syntax.term list) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 2659 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_nonempty_list_term_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState175)
    | MenhirState253 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let ((((_menhir_stack, _menhir_s, _startpos__1_), _), _, (_3 : (Smtlib_syntax.symbol * Smtlib_syntax.symbol list *
  Smtlib_syntax.sorted_var list * Smtlib_syntax.sort))), _, (_4 : (Smtlib_syntax.term))) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__5_ in
            let _startpos = _startpos__1_ in
            
# 287 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_DefineFunRec (_3,_4)) )
# 2684 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState257 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__5_ = _endpos in
            let ((((_menhir_stack, _menhir_s, _startpos__1_), _), _, (_3 : (Smtlib_syntax.symbol * Smtlib_syntax.symbol list *
  Smtlib_syntax.sorted_var list * Smtlib_syntax.sort))), _, (_4 : (Smtlib_syntax.term))) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__5_ in
            let _startpos = _startpos__1_ in
            
# 285 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_DefineFun (_3,_4)) )
# 2711 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState357 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__7_ = _endpos in
            let ((((((_menhir_stack, _menhir_s, _startpos__1_), _), _startpos__3_), _, (_4 : (Smtlib_syntax.symbol list))), _endpos__5_), _, (_6 : (Smtlib_syntax.term))) = _menhir_stack in
            let _v : (Smtlib_syntax.symbol list * Smtlib_syntax.term) = 
# 259 "src/lib/smtlib_parser.mly"
        ( _4,_6 )
# 2735 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_assert_dec _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState366 | MenhirState352 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (_1 : (Smtlib_syntax.term))) = _menhir_stack in
        let _v : (Smtlib_syntax.symbol list * Smtlib_syntax.term) = 
# 257 "src/lib/smtlib_parser.mly"
        ( [],_1 )
# 2751 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_assert_dec _menhir_env _menhir_stack _menhir_s _v
    | MenhirState369 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Smtlib_syntax.symbol)), _startpos__2_), _, (_3 : (Smtlib_syntax.term))) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__4_ in
            let _startpos = _startpos__1_ in
            
# 329 "src/lib/smtlib_parser.mly"
                      (
         let { c = cmd; p; _ } = _2 in
         let t = _3 in
         match cmd with
         | "minimize" -> mk_data (_startpos,_endpos) (Cmd_Minimize t)
         | "maximize" -> mk_data (_startpos,_endpos) (Cmd_Maximize t)
         | _ ->
            let err = Format.sprintf "Unexpected command %S" cmd in
            raise Smtlib_error.(Error (Syntax_error err, p))
       )
# 2780 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState376 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (_1 : (Smtlib_syntax.term))) = _menhir_stack in
        Obj.magic _1
    | MenhirState380 | MenhirState378 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState380 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | BINARY _v ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState380 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DECIMAL _v ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState380 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HEXADECIMAL _v ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState380 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState380 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUMERAL _v ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState380 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STRINGLIT _v ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState380 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState380 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState380)
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_prop_literal : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.prop_literal_aux Smtlib_syntax.data) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState345 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LP ->
        _menhir_run340 _menhir_env (Obj.magic _menhir_stack) MenhirState345 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState345 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | RP ->
        _menhir_reduce113 _menhir_env (Obj.magic _menhir_stack) MenhirState345
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState345

and _menhir_run127 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | UNDERSCORE ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState127 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState127

and _menhir_run294 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LP ->
        _menhir_run300 _menhir_env (Obj.magic _menhir_stack) MenhirState294 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | PAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState294 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState296 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState296 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState296)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState294

and _menhir_reduce115 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Smtlib_syntax.selector_dec list) = 
# 211 "<standard.mly>"
    ( [] )
# 2906 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_list_selector_dec_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run302 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState302 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState302 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState302

and _menhir_goto_nonempty_list_sort_dec_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.sort_dec list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState289 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Smtlib_syntax.sort_dec))), _, (xs : (Smtlib_syntax.sort_dec list))) = _menhir_stack in
        let _v : (Smtlib_syntax.sort_dec list) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 2936 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_nonempty_list_sort_dec_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState284 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LP ->
                    _menhir_run294 _menhir_env (Obj.magic _menhir_stack) MenhirState293 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState293)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce119 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Smtlib_syntax.sort list) = 
# 211 "<standard.mly>"
    ( [] )
# 2984 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_list_sort_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce121 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Smtlib_syntax.sorted_var list) = 
# 211 "<standard.mly>"
    ( [] )
# 2993 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_list_sorted_var_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run155 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState155 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState155 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState155

and _menhir_goto_key_term : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.key_term) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | NAMED ->
        _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | PATTERN ->
        _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState183 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | RP ->
        _menhir_reduce111 _menhir_env (Obj.magic _menhir_stack) MenhirState183
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState183

and _menhir_run129 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LP ->
        _menhir_run127 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UNDERSCORE ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState129 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState129

and _menhir_goto_identifier : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (Smtlib_syntax.identifier) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState378 | MenhirState380 | MenhirState376 | MenhirState369 | MenhirState366 | MenhirState352 | MenhirState353 | MenhirState357 | MenhirState257 | MenhirState253 | MenhirState246 | MenhirState93 | MenhirState94 | MenhirState185 | MenhirState171 | MenhirState174 | MenhirState175 | MenhirState168 | MenhirState162 | MenhirState150 | MenhirState144 | MenhirState140 | MenhirState101 | MenhirState113 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.identifier)), _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__1_ in
        let _v : (Smtlib_syntax.qualidentifier) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 124 "src/lib/smtlib_parser.mly"
                 ( mk_data (_startpos,_endpos) (QualIdentifierId _1) )
# 3064 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_qualidentifier _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState126 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState128 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState128 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState128 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState128)
    | MenhirState328 | MenhirState129 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState130 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState130 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState130)
    | MenhirState327 | MenhirState332 | MenhirState303 | MenhirState266 | MenhirState279 | MenhirState271 | MenhirState275 | MenhirState272 | MenhirState240 | MenhirState236 | MenhirState220 | MenhirState156 | MenhirState128 | MenhirState130 | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.identifier)), _startpos__1_) = _menhir_stack in
        let _v : (Smtlib_syntax.sort) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 95 "src/lib/smtlib_parser.mly"
                 ( mk_data (_startpos,_endpos) (SortIdentifier _1) )
# 3106 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_sort _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_pattern : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.pattern_aux Smtlib_syntax.data) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState113 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | BINARY _v ->
        _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState113 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DECIMAL _v ->
        _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState113 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | HEXADECIMAL _v ->
        _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState113 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LP ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState113 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUMERAL _v ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState113 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRINGLIT _v ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState113 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState113 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState113

and _menhir_goto_nonempty_list_symbol_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.symbol list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState108 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _endpos_x_, _menhir_s, (x : (Smtlib_syntax.symbol)), _startpos_x_), _, (xs : (Smtlib_syntax.symbol list))) = _menhir_stack in
        let _v : (Smtlib_syntax.symbol list) = 
# 223 "<standard.mly>"
    ( x :: xs )
# 3151 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_nonempty_list_symbol_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Smtlib_syntax.symbol)), _startpos__2_), _, (_3 : (Smtlib_syntax.symbol list))) = _menhir_stack in
            let _v : (Smtlib_syntax.pattern_aux Smtlib_syntax.data) = let _endpos = _endpos__4_ in
            let _startpos = _startpos__1_ in
            
# 132 "src/lib/smtlib_parser.mly"
       ( mk_data (_startpos,_endpos) (MatchPattern (_2, _3)) )
# 3171 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState229 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LP ->
                    _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState232 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | RP ->
                    _menhir_reduce121 _menhir_env (Obj.magic _menhir_stack) MenhirState232
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState232)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState268 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | ASCIIWOR _v ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState271 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | LP ->
                    _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState271 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | SYMBOL _v ->
                    _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState271 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | RP ->
                    _menhir_reduce119 _menhir_env (Obj.magic _menhir_stack) MenhirState271
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState271)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState296 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                let _menhir_stack = (_menhir_stack, _startpos) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LP ->
                    _menhir_run300 _menhir_env (Obj.magic _menhir_stack) MenhirState299 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState299)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState330 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState332 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState332 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState332 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState332)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState355 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState357 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | BINARY _v ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState357 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DECIMAL _v ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState357 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | HEXADECIMAL _v ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState357 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState357 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUMERAL _v ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState357 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRINGLIT _v ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState357 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState357 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState357)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run52 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 3371 "src/lib/smtlib_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let (_1 : (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 3380 "src/lib/smtlib_parser.ml"
    )) = _v in
    let _startpos__1_ = _startpos in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.index) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 79 "src/lib/smtlib_parser.mly"
               ( mk_data (_startpos,_endpos) (IndexNumeral _1) )
# 3389 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_index _menhir_env _menhir_stack _endpos _menhir_s _v

and _menhir_goto_attribute_value : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (Smtlib_syntax.attribute_value_aux Smtlib_syntax.data) -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__2_ = _endpos in
    let (_2 : (Smtlib_syntax.attribute_value_aux Smtlib_syntax.data)) = _v in
    let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.key_info_aux Smtlib_syntax.data)), _startpos__1_) = _menhir_stack in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__2_ in
    let _v : (Smtlib_syntax.attribute) = let _endpos = _endpos__2_ in
    let _startpos = _startpos__1_ in
    
# 108 "src/lib/smtlib_parser.mly"
        ( mk_data (_startpos,_endpos) (AttributeKeyValue(_1,_2)) )
# 3407 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_attribute _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_goto_sexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.sexpr) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | AXIOMS ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | BINARY _v ->
        _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | CATEGORY ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DECIMAL _v ->
        _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DEFINITIO ->
        _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXTENSIONS ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FUNS ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | FUNSDESCRIPT ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | HEXADECIMAL _v ->
        _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LANGUAGE ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LICENSE ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LP ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NOTES ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUMERAL _v ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SMTLIBVERSION ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SORTS ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SORTSDESCRIPTION ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SOURCE ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STATUTS ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRINGLIT _v ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | THEORIES ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | VALUES ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState64 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | RP ->
        _menhir_reduce117 _menhir_env (Obj.magic _menhir_stack) MenhirState64
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState64

and _menhir_goto_index : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (Smtlib_syntax.index) -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState51 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (_1 : (Smtlib_syntax.key_option)), _startpos__1_), _endpos__2_, _, (_2 : (Smtlib_syntax.index))) = _menhir_stack in
        let _v : (Smtlib_syntax.option_aux Smtlib_syntax.data) = let _endpos = _endpos__2_ in
        let _startpos = _startpos__1_ in
        
# 193 "src/lib/smtlib_parser.mly"
                       (mk_data (_startpos,_endpos) (Option_key (_1,_2)) )
# 3486 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_src_lib_smtlib_parser_option _menhir_env _menhir_stack _menhir_s _v
    | MenhirState99 | MenhirState96 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState99 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUMERAL _v ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState99 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState99 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_x_, _menhir_s, (x : (Smtlib_syntax.index))) = _menhir_stack in
            let _v : (Smtlib_syntax.index list) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 3506 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_nonempty_list_index_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState99)
    | _ ->
        _menhir_fail ()

and _menhir_goto_keyword : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (Smtlib_syntax.keyword) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState202 | MenhirState79 | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.keyword)), _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__1_ in
        let _v : (Smtlib_syntax.key_info_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 209 "src/lib/smtlib_parser.mly"
              (mk_data (_startpos,_endpos) (Key_info _1) )
# 3531 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_key_info _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState58 | MenhirState59 | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.keyword)), _startpos__1_) = _menhir_stack in
        let _v : (Smtlib_syntax.sexpr) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 113 "src/lib/smtlib_parser.mly"
              ( mk_data (_startpos,_endpos) (SexprKeyword _1) )
# 3543 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_sexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState197 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _), _endpos__3_, _, (_3 : (Smtlib_syntax.keyword)), _startpos__3_) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__4_ in
            let _startpos = _startpos__1_ in
            
# 305 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_GetOption _3) )
# 3563 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_key_option : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.key_option) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState51 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUMERAL _v ->
        _menhir_run52 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState51 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState51 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState51

and _menhir_run4 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.key_info_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 208 "src/lib/smtlib_parser.mly"
              (mk_data (_startpos,_endpos) Version )
# 3606 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_key_info _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run6 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 173 "src/lib/smtlib_parser.mly"
             (mk_data (_startpos,_endpos) Values )
# 3623 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run7 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 172 "src/lib/smtlib_parser.mly"
               (mk_data (_startpos,_endpos) Theories )
# 3640 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run8 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState8 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState8 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState8

and _menhir_run11 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 159 "src/lib/smtlib_parser.mly"
             (mk_data (_startpos,_endpos) Source )
# 3672 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run12 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 171 "src/lib/smtlib_parser.mly"
                       (mk_data (_startpos,_endpos) SortsDescr )
# 3689 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run13 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 170 "src/lib/smtlib_parser.mly"
            (mk_data (_startpos,_endpos) Sorts )
# 3706 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run14 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 158 "src/lib/smtlib_parser.mly"
                    (mk_data (_startpos,_endpos) Smtlibversion )
# 3723 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run15 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.key_info_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 207 "src/lib/smtlib_parser.mly"
             (mk_data (_startpos,_endpos) Series )
# 3740 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_key_info _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run18 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.key_info_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 206 "src/lib/smtlib_parser.mly"
                    (mk_data (_startpos,_endpos) Reasonunknown )
# 3757 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_key_info _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run27 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 163 "src/lib/smtlib_parser.mly"
            (mk_data (_startpos,_endpos) Notes )
# 3774 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run28 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.key_info_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 205 "src/lib/smtlib_parser.mly"
           (mk_data (_startpos,_endpos) Name )
# 3791 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_key_info _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run29 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 162 "src/lib/smtlib_parser.mly"
              (mk_data (_startpos,_endpos) License )
# 3808 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run30 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 169 "src/lib/smtlib_parser.mly"
               (mk_data (_startpos,_endpos) Language )
# 3825 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run32 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.key_info_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 204 "src/lib/smtlib_parser.mly"
               (mk_data (_startpos,_endpos) Instance )
# 3842 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_key_info _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run33 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.key_info_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 203 "src/lib/smtlib_parser.mly"
                  (mk_data (_startpos,_endpos) Incremental )
# 3859 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_key_info _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run35 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 168 "src/lib/smtlib_parser.mly"
                   (mk_data (_startpos,_endpos) FunsDescript  )
# 3876 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run36 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 167 "src/lib/smtlib_parser.mly"
           (mk_data (_startpos,_endpos) Funs )
# 3893 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run37 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 166 "src/lib/smtlib_parser.mly"
                 (mk_data (_startpos,_endpos) Extensions )
# 3910 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run38 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.key_info_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 202 "src/lib/smtlib_parser.mly"
                 (mk_data (_startpos,_endpos) Errorbehav )
# 3927 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_key_info _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run39 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.key_info_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 201 "src/lib/smtlib_parser.mly"
                 (mk_data (_startpos,_endpos) Difficulty )
# 3944 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_key_info _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run41 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 165 "src/lib/smtlib_parser.mly"
                (mk_data (_startpos,_endpos) Definitio )
# 3961 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run42 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 157 "src/lib/smtlib_parser.mly"
               (mk_data (_startpos,_endpos) Category )
# 3978 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run43 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 164 "src/lib/smtlib_parser.mly"
             (mk_data (_startpos,_endpos) Axioms )
# 3995 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run44 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.key_info_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 199 "src/lib/smtlib_parser.mly"
              (mk_data (_startpos,_endpos) Authors )
# 4012 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_key_info _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run45 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.key_info_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 200 "src/lib/smtlib_parser.mly"
             (mk_data (_startpos,_endpos) Authors )
# 4029 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_key_info _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run46 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.key_info_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 198 "src/lib/smtlib_parser.mly"
                        (mk_data (_startpos,_endpos) Assertionstacklvl )
# 4046 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_key_info _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run47 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.key_info_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 197 "src/lib/smtlib_parser.mly"
               (mk_data (_startpos,_endpos) Allstats )
# 4063 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_key_info _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_reduce109 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : ((Smtlib_syntax.symbol * Smtlib_syntax.symbol list *
   Smtlib_syntax.sorted_var list * Smtlib_syntax.sort)
  list) = 
# 211 "<standard.mly>"
    ( [] )
# 4074 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_list_fun_defs_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run225 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState225 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState225 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState225

and _menhir_run285 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState285 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState285 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState285

and _menhir_reduce113 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Smtlib_syntax.prop_literal list) = 
# 211 "<standard.mly>"
    ( [] )
# 4113 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_list_prop_literal_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run340 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState340 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState340 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState340

and _menhir_goto_command : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.command) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EOF ->
        _menhir_run372 _menhir_env (Obj.magic _menhir_stack) MenhirState374
    | LP ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState374 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState374

and _menhir_reduce123 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Smtlib_syntax.symbol list) = 
# 211 "<standard.mly>"
    ( [] )
# 4153 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_list_symbol_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run353 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AS ->
        _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState353
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState353 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXCLIMATIONPT ->
        _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState353
    | EXISTS ->
        _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState353
    | FORALL ->
        _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState353
    | LET ->
        _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState353
    | LP ->
        _menhir_run125 _menhir_env (Obj.magic _menhir_stack) MenhirState353 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState353
    | PAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState353 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState355 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState355 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState355)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState353 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UNDERSCORE ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState353 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState353

and _menhir_goto_commands : _menhir_env -> 'ttv_tail -> _menhir_state -> (Smtlib_syntax.commands) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_1 : (Smtlib_syntax.commands)) = _v in
        Obj.magic _1
    | MenhirState374 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_2 : (Smtlib_syntax.commands)) = _v in
        let (_menhir_stack, _menhir_s, (_1 : (Smtlib_syntax.command))) = _menhir_stack in
        let _v : (Smtlib_syntax.commands) = 
# 343 "src/lib/smtlib_parser.mly"
                       ( _1::_2 )
# 4232 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_commands _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run95 : _menhir_env -> 'ttv_tail * _menhir_state * Lexing.position -> Lexing.position -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState95 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState95

and _menhir_run101 : _menhir_env -> 'ttv_tail * _menhir_state * Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | BINARY _v ->
        _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DECIMAL _v ->
        _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | HEXADECIMAL _v ->
        _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LP ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUMERAL _v ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRINGLIT _v ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState101 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState101

and _menhir_run125 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AS ->
        _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState125
    | UNDERSCORE ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState125 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState125

and _menhir_run138 : _menhir_env -> 'ttv_tail * _menhir_state * Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LP ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState139 in
            let _menhir_stack = (_menhir_stack, _endpos, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState140 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | BINARY _v ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState140 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DECIMAL _v ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState140 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | HEXADECIMAL _v ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState140 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUMERAL _v ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState140 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRINGLIT _v ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState140 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState140 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState140)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState139)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run153 : _menhir_env -> 'ttv_tail * _menhir_state * Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LP ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState154)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run165 : _menhir_env -> 'ttv_tail * _menhir_state * Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LP ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = (_menhir_stack, _startpos) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState166)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run171 : _menhir_env -> 'ttv_tail * _menhir_state * Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | BINARY _v ->
        _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DECIMAL _v ->
        _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | HEXADECIMAL _v ->
        _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LP ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUMERAL _v ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRINGLIT _v ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState171 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState171

and _menhir_run126 : _menhir_env -> 'ttv_tail * _menhir_state * Lexing.position -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState126 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LP ->
        _menhir_run127 _menhir_env (Obj.magic _menhir_stack) MenhirState126 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState126 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState126

and _menhir_goto_constant : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (Smtlib_syntax.constant) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    match _menhir_s with
    | MenhirState58 | MenhirState59 | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__1_ = _endpos in
        let (_1 : (Smtlib_syntax.constant)) = _v in
        let _startpos__1_ = _startpos in
        let _v : (Smtlib_syntax.sexpr) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 111 "src/lib/smtlib_parser.mly"
               ( mk_data (_startpos,_endpos) (SexprSpecConst _1) )
# 4459 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_sexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__1_ = _endpos in
        let (_1 : (Smtlib_syntax.constant)) = _v in
        let _startpos__1_ = _startpos in
        let _endpos = _endpos__1_ in
        let _v : (Smtlib_syntax.attribute_value_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 101 "src/lib/smtlib_parser.mly"
               ( mk_data (_startpos,_endpos) (AttributeValSpecConst _1) )
# 4474 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_attribute_value _menhir_env _menhir_stack _endpos _menhir_s _v
    | MenhirState378 | MenhirState380 | MenhirState376 | MenhirState369 | MenhirState366 | MenhirState352 | MenhirState357 | MenhirState257 | MenhirState253 | MenhirState246 | MenhirState93 | MenhirState185 | MenhirState171 | MenhirState174 | MenhirState175 | MenhirState168 | MenhirState162 | MenhirState150 | MenhirState144 | MenhirState140 | MenhirState101 | MenhirState113 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _endpos__1_ = _endpos in
        let (_1 : (Smtlib_syntax.constant)) = _v in
        let _startpos__1_ = _startpos in
        let _v : (Smtlib_syntax.term) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 138 "src/lib/smtlib_parser.mly"
               ( mk_data (_startpos,_endpos) (TermSpecConst _1) )
# 4488 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_term _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_symbol : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (Smtlib_syntax.symbol) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_stack = (_menhir_stack, _endpos, _menhir_s, _v, _startpos) in
    match _menhir_s with
    | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Smtlib_syntax.symbol)), _startpos__2_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__2_ in
        let _v : (Smtlib_syntax.keyword) = let _endpos = _endpos__2_ in
        let _startpos = _startpos__1_ in
        
# 161 "src/lib/smtlib_parser.mly"
        (Options.set_status _2.c;mk_data (_startpos,_endpos) (Statuts _2) )
# 4509 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_keyword _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState99 | MenhirState96 | MenhirState51 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.symbol)), _startpos__1_) = _menhir_stack in
        let _endpos = _endpos__1_ in
        let _v : (Smtlib_syntax.index) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 78 "src/lib/smtlib_parser.mly"
               ( mk_data (_startpos,_endpos) (IndexSymbol _1) )
# 4522 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_index _menhir_env _menhir_stack _endpos _menhir_s _v
    | MenhirState58 | MenhirState64 | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.symbol)), _startpos__1_) = _menhir_stack in
        let _v : (Smtlib_syntax.sexpr) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 112 "src/lib/smtlib_parser.mly"
             ( mk_data (_startpos,_endpos) (SexprSymbol _1) )
# 4534 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_sexpr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.symbol)), _startpos__1_) = _menhir_stack in
        let _endpos = _endpos__1_ in
        let _v : (Smtlib_syntax.attribute_value_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 102 "src/lib/smtlib_parser.mly"
             ( mk_data (_startpos,_endpos) (AttributeValSymbol _1) )
# 4547 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_attribute_value _menhir_env _menhir_stack _endpos _menhir_s _v
    | MenhirState76 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _), _endpos__3_, _, (_3 : (Smtlib_syntax.symbol)), _startpos__3_) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__4_ in
            let _startpos = _startpos__1_ in
            
# 325 "src/lib/smtlib_parser.mly"
        (Options.set_logic true;
         mk_data (_startpos,_endpos) (Cmd_SetLogic _3) )
# 4568 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState95 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState96 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUMERAL _v ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState96 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState96 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState96)
    | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState107 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState107 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState107)
    | MenhirState355 | MenhirState330 | MenhirState296 | MenhirState268 | MenhirState229 | MenhirState108 | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState108 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState108 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _endpos_x_, _menhir_s, (x : (Smtlib_syntax.symbol)), _startpos_x_) = _menhir_stack in
            let _v : (Smtlib_syntax.symbol list) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 4620 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_nonempty_list_symbol_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState108)
    | MenhirState104 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.symbol)), _startpos__1_) = _menhir_stack in
        let _v : (Smtlib_syntax.pattern_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 129 "src/lib/smtlib_parser.mly"
             ( mk_data (_startpos,_endpos) (MatchPattern (_1, [])) )
# 4636 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v
    | MenhirState378 | MenhirState380 | MenhirState376 | MenhirState369 | MenhirState366 | MenhirState352 | MenhirState353 | MenhirState357 | MenhirState327 | MenhirState328 | MenhirState332 | MenhirState303 | MenhirState279 | MenhirState266 | MenhirState275 | MenhirState272 | MenhirState271 | MenhirState257 | MenhirState253 | MenhirState246 | MenhirState240 | MenhirState236 | MenhirState220 | MenhirState93 | MenhirState185 | MenhirState94 | MenhirState171 | MenhirState174 | MenhirState175 | MenhirState168 | MenhirState162 | MenhirState156 | MenhirState150 | MenhirState144 | MenhirState140 | MenhirState128 | MenhirState131 | MenhirState130 | MenhirState129 | MenhirState126 | MenhirState101 | MenhirState113 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.symbol)), _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos__1_ in
        let _v : (Smtlib_syntax.identifier) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 82 "src/lib/smtlib_parser.mly"
             ( mk_data (_startpos,_endpos) (IdSymbol _1) )
# 4650 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_identifier _menhir_env _menhir_stack _endpos _menhir_s _v _startpos
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState144 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | BINARY _v ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState144 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DECIMAL _v ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState144 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HEXADECIMAL _v ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState144 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState144 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUMERAL _v ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState144 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STRINGLIT _v ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState144 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState144 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState144)
    | MenhirState155 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState156 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState156)
    | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Smtlib_syntax.symbol)), _startpos__2_) = _menhir_stack in
        let _v : (Smtlib_syntax.key_term) = let _endpos = _endpos__2_ in
        let _startpos = _startpos__1_ in
        
# 214 "src/lib/smtlib_parser.mly"
                   ( mk_data (_startpos,_endpos) (Named _2) )
# 4702 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_key_term _menhir_env _menhir_stack _menhir_s _v
    | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _), _endpos__3_, _, (_3 : (Smtlib_syntax.symbol)), _startpos__3_) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__4_ in
            let _startpos = _startpos__1_ in
            
# 293 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_Echo _3) )
# 4722 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState214 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState216 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState216 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RP ->
                _menhir_reduce123 _menhir_env (Obj.magic _menhir_stack) MenhirState216
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState216)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState363 | MenhirState217 | MenhirState216 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState217 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState217 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RP ->
            _menhir_reduce123 _menhir_env (Obj.magic _menhir_stack) MenhirState217
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState217)
    | MenhirState256 | MenhirState252 | MenhirState225 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LP ->
                _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | PAR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_s = MenhirState227 in
                let _menhir_stack = (_menhir_stack, _menhir_s) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LP ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                    let _menhir_stack = (_menhir_stack, _startpos) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | ASCIIWOR _v ->
                        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState229 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | SYMBOL _v ->
                        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState229 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState229)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | RP ->
                _menhir_reduce121 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState227)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState260 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | NUMERAL _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__5_ = _endpos in
                let ((((_menhir_stack, _menhir_s, _startpos__1_), _), _endpos__3_, _, (_3 : (Smtlib_syntax.symbol)), _startpos__3_), _endpos__4_, (_4 : (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 4850 "src/lib/smtlib_parser.ml"
                )), _startpos__4_) = _menhir_stack in
                let _v : (Smtlib_syntax.command) = let _endpos = _endpos__5_ in
                let _startpos = _startpos__1_ in
                
# 283 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_DeclareSort (_3, _4)) )
# 4857 "src/lib/smtlib_parser.ml"
                 in
                _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _, _menhir_s, _, _), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState264 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState266 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState266 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | PAR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_s = MenhirState266 in
                let _menhir_stack = (_menhir_stack, _menhir_s) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LP ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                    let _menhir_stack = (_menhir_stack, _startpos) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | ASCIIWOR _v ->
                        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState268 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | SYMBOL _v ->
                        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState268 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState268)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState266 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RP ->
                _menhir_reduce119 _menhir_env (Obj.magic _menhir_stack) MenhirState266
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState266)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState285 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | NUMERAL _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__4_ = _endpos in
                let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Smtlib_syntax.symbol)), _startpos__2_), _endpos__3_, (_3 : (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 4952 "src/lib/smtlib_parser.ml"
                )), _startpos__3_) = _menhir_stack in
                let _v : (Smtlib_syntax.sort_dec) = 
# 230 "src/lib/smtlib_parser.mly"
                           ( (_2,_3) )
# 4957 "src/lib/smtlib_parser.ml"
                 in
                let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
                let _menhir_stack = Obj.magic _menhir_stack in
                assert (not _menhir_env._menhir_error);
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LP ->
                    _menhir_run285 _menhir_env (Obj.magic _menhir_stack) MenhirState289 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                | RP ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, (x : (Smtlib_syntax.sort_dec))) = _menhir_stack in
                    let _v : (Smtlib_syntax.sort_dec list) = 
# 221 "<standard.mly>"
    ( [ x ] )
# 4972 "src/lib/smtlib_parser.ml"
                     in
                    _menhir_goto_nonempty_list_sort_dec_ _menhir_env _menhir_stack _menhir_s _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState289)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _, _menhir_s, _, _), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState300 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            _menhir_run302 _menhir_env (Obj.magic _menhir_stack) MenhirState301 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RP ->
            _menhir_reduce115 _menhir_env (Obj.magic _menhir_stack) MenhirState301
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState301)
    | MenhirState302 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState303 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState303 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState303 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState303)
    | MenhirState322 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            _menhir_run294 _menhir_env (Obj.magic _menhir_stack) MenhirState323 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState323)
    | MenhirState326 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState327 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState327 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState328 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run127 _menhir_env (Obj.magic _menhir_stack) MenhirState328 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | PAR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_s = MenhirState328 in
                let _menhir_stack = (_menhir_stack, _menhir_s) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LP ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
                    let _menhir_stack = (_menhir_stack, _startpos) in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | ASCIIWOR _v ->
                        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState330 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | SYMBOL _v ->
                        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState330 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState330)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState328 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | UNDERSCORE ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState328 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState328)
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState327 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState327)
    | MenhirState340 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState341 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState341 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState341)
    | MenhirState341 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__4_ = _endpos in
            let (((_menhir_stack, _menhir_s, _startpos__1_), _endpos__2_, _, (_2 : (Smtlib_syntax.symbol)), _startpos__2_), _endpos__3_, _, (_3 : (Smtlib_syntax.symbol)), _startpos__3_) = _menhir_stack in
            let _v : (Smtlib_syntax.prop_literal_aux Smtlib_syntax.data) = let _endpos = _endpos__4_ in
            let _startpos = _startpos__1_ in
            
# 90 "src/lib/smtlib_parser.mly"
      ( mk_data (_startpos,_endpos)
        (if _2.c <> "not" then failwith "Prop literal can only be literal and negated literal"
            ; PropLitNot _3) )
# 5123 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_prop_literal _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState345 | MenhirState339 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _endpos__1_, _menhir_s, (_1 : (Smtlib_syntax.symbol)), _startpos__1_) = _menhir_stack in
        let _v : (Smtlib_syntax.prop_literal_aux Smtlib_syntax.data) = let _endpos = _endpos__1_ in
        let _startpos = _startpos__1_ in
        
# 88 "src/lib/smtlib_parser.mly"
      ( mk_data (_startpos,_endpos) (PropLit _1) )
# 5141 "src/lib/smtlib_parser.ml"
         in
        _menhir_goto_prop_literal _menhir_env _menhir_stack _menhir_s _v
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState369 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | BINARY _v ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState369 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DECIMAL _v ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState369 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HEXADECIMAL _v ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState369 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState369 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUMERAL _v ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState369 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STRINGLIT _v ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState369 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState369 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState369)
    | _ ->
        _menhir_fail ()

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState1 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | ASSERT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState366 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | BINARY _v ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState366 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DECIMAL _v ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState366 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HEXADECIMAL _v ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState366 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run353 _menhir_env (Obj.magic _menhir_stack) MenhirState366 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUMERAL _v ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState366 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STRINGLIT _v ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState366 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState366 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState366)
    | CHECKALLSAT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState363 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState363 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | RP ->
            _menhir_reduce123 _menhir_env (Obj.magic _menhir_stack) MenhirState363
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState363)
    | CHECKENTAILMENT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | BINARY _v ->
            _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DECIMAL _v ->
            _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | HEXADECIMAL _v ->
            _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LP ->
            _menhir_run353 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NUMERAL _v ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STRINGLIT _v ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState352 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState352)
    | CHECKSAT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__3_ in
            let _startpos = _startpos__1_ in
            
# 266 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_CheckSat) )
# 5270 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | CHECKSATASSUMING ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState339 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run340 _menhir_env (Obj.magic _menhir_stack) MenhirState339 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState339 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RP ->
                _menhir_reduce113 _menhir_env (Obj.magic _menhir_stack) MenhirState339
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState339)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | DECLARECONST ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState326 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState326 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState326)
    | DECLAREDATATYPE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState322 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState322 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState322)
    | DECLAREDATATYPES ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LP ->
                _menhir_run285 _menhir_env (Obj.magic _menhir_stack) MenhirState284 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState284)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | DECLAREFUN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState264 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState264 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState264)
    | DECLARESORT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState260 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState260 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState260)
    | DEFINEFUN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState256 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState256 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState256)
    | DEFINEFUNREC ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState252 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState252 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState252)
    | DEFINEFUNSREC ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LP ->
                _menhir_run225 _menhir_env (Obj.magic _menhir_stack) MenhirState224 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | RP ->
                _menhir_reduce109 _menhir_env (Obj.magic _menhir_stack) MenhirState224
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState224)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | DEFINESORT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState214 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState214)
    | ECHO ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState211 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState211 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState211)
    | EXIT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__3_ in
            let _startpos = _startpos__1_ in
            
# 295 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_Exit) )
# 5504 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | GETASSERT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__3_ in
            let _startpos = _startpos__1_ in
            
# 297 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_GetAssert) )
# 5532 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | GETASSIGN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__3_ in
            let _startpos = _startpos__1_ in
            
# 299 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_GetAssign) )
# 5560 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | GETINFO ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ALLSTATS ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ASSERTIONSTACKLVL ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AUTHOR ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AUTHORS ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AXIOMS ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | CATEGORY ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DEFINITIO ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DIFFICULTY ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ERRORBEHAV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EXTENSIONS ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | FUNS ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | FUNSDESCRIPT ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INCREMENTAL ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INSTANCE ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LANGUAGE ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LICENSE ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NAME ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTES ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | REASONUNKNOWN ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SERIES ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SMTLIBVERSION ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SORTS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SORTSDESCRIPTION ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SOURCE ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STATUTS ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | THEORIES ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | VALUES ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | VERSION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState202 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState202)
    | GETMODEL ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__3_ in
            let _startpos = _startpos__1_ in
            
# 303 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_GetModel) )
# 5655 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | GETOPTION ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AXIOMS ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | CATEGORY ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DEFINITIO ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EXTENSIONS ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | FUNS ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | FUNSDESCRIPT ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LANGUAGE ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LICENSE ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTES ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SMTLIBVERSION ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SORTS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SORTSDESCRIPTION ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SOURCE ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STATUTS ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | THEORIES ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | VALUES ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState197 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState197)
    | GETPROOF ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__3_ in
            let _startpos = _startpos__1_ in
            
# 307 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_GetProof) )
# 5726 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | GETUNSATASSUMPTIONS ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__3_ in
            let _startpos = _startpos__1_ in
            
# 309 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_GetUnsatAssumptions) )
# 5754 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | GETUNSATCORE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__3_ in
            let _startpos = _startpos__1_ in
            
# 311 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_GetUnsatCore) )
# 5782 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | GETVALUE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ASCIIWOR _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | BINARY _v ->
                _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | DECIMAL _v ->
                _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | HEXADECIMAL _v ->
                _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | LP ->
                _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | NUMERAL _v ->
                _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | STRINGLIT _v ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | SYMBOL _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState93 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState93)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | POP ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | NUMERAL _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__4_ = _endpos in
                let (((_menhir_stack, _menhir_s, _startpos__1_), _), _endpos__3_, (_3 : (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 5855 "src/lib/smtlib_parser.ml"
                )), _startpos__3_) = _menhir_stack in
                let _v : (Smtlib_syntax.command) = let _endpos = _endpos__4_ in
                let _startpos = _startpos__1_ in
                
# 317 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_Pop _3) )
# 5862 "src/lib/smtlib_parser.ml"
                 in
                _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | PUSH ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | NUMERAL _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_stack = (_menhir_stack, _endpos, _v, _startpos) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | RP ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _endpos__4_ = _endpos in
                let (((_menhir_stack, _menhir_s, _startpos__1_), _), _endpos__3_, (_3 : (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 5901 "src/lib/smtlib_parser.ml"
                )), _startpos__3_) = _menhir_stack in
                let _v : (Smtlib_syntax.command) = let _endpos = _endpos__4_ in
                let _startpos = _startpos__1_ in
                
# 315 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_Push _3) )
# 5908 "src/lib/smtlib_parser.ml"
                 in
                _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _, _, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | RESET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__3_ in
            let _startpos = _startpos__1_ in
            
# 319 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_Reset) )
# 5942 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | RESETASSERTIONS ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RP ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _) = _menhir_stack in
            let _v : (Smtlib_syntax.command) = let _endpos = _endpos__3_ in
            let _startpos = _startpos__1_ in
            
# 321 "src/lib/smtlib_parser.mly"
        (mk_data (_startpos,_endpos) (Cmd_ResetAssert) )
# 5970 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | SETINFO ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ALLSTATS ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ASSERTIONSTACKLVL ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AUTHOR ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AUTHORS ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AXIOMS ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | CATEGORY ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DEFINITIO ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DIFFICULTY ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ERRORBEHAV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EXTENSIONS ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | FUNS ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | FUNSDESCRIPT ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INCREMENTAL ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INSTANCE ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LANGUAGE ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LICENSE ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NAME ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTES ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | REASONUNKNOWN ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SERIES ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SMTLIBVERSION ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SORTS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SORTSDESCRIPTION ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SOURCE ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STATUTS ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | THEORIES ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | VALUES ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | VERSION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState79 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState79)
    | SETLOGIC ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ASCIIWOR _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState76 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SYMBOL _v ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState76 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState76)
    | SETOPTION ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState1 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ALLSTATS ->
            _menhir_run47 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ASSERTIONSTACKLVL ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AUTHOR ->
            _menhir_run45 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AUTHORS ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | AXIOMS ->
            _menhir_run43 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | CATEGORY ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DEFINITIO ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | DIAGNOOUTPUTCHAN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState3 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__1_ = _endpos in
            let _startpos__1_ = _startpos in
            let _startpos = _startpos__1_ in
            let _v : (Smtlib_syntax.key_option) = let _endpos = _endpos__1_ in
            let _startpos = _startpos__1_ in
            
# 176 "src/lib/smtlib_parser.mly"
                       (mk_data (_startpos,_endpos) Diagnooutputchan )
# 6097 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_key_option _menhir_env _menhir_stack _menhir_s _v _startpos
        | DIFFICULTY ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | ERRORBEHAV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | EXTENSIONS ->
            _menhir_run37 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | FUNS ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | FUNSDESCRIPT ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | GLOBALDECLARATIONS ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState3 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__1_ = _endpos in
            let _startpos__1_ = _startpos in
            let _startpos = _startpos__1_ in
            let _v : (Smtlib_syntax.key_option) = let _endpos = _endpos__1_ in
            let _startpos = _startpos__1_ in
            
# 177 "src/lib/smtlib_parser.mly"
                         (mk_data (_startpos,_endpos) Globaldeclarations )
# 6125 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_key_option _menhir_env _menhir_stack _menhir_s _v _startpos
        | INCREMENTAL ->
            _menhir_run33 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INSTANCE ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | INTERACTIVE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState3 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__1_ = _endpos in
            let _startpos__1_ = _startpos in
            let _startpos = _startpos__1_ in
            let _v : (Smtlib_syntax.key_option) = let _endpos = _endpos__1_ in
            let _startpos = _startpos__1_ in
            
# 178 "src/lib/smtlib_parser.mly"
                  (mk_data (_startpos,_endpos) Interactive )
# 6147 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_key_option _menhir_env _menhir_stack _menhir_s _v _startpos
        | LANGUAGE ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | LICENSE ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NAME ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | NOTES ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | PRINTSUCCESS ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState3 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__1_ = _endpos in
            let _startpos__1_ = _startpos in
            let _startpos = _startpos__1_ in
            let _v : (Smtlib_syntax.key_option) = let _endpos = _endpos__1_ in
            let _startpos = _startpos__1_ in
            
# 179 "src/lib/smtlib_parser.mly"
                   (mk_data (_startpos,_endpos) Printsucces )
# 6173 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_key_option _menhir_env _menhir_stack _menhir_s _v _startpos
        | PRODUCEASSERTIONS ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState3 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__1_ = _endpos in
            let _startpos__1_ = _startpos in
            let _startpos = _startpos__1_ in
            let _v : (Smtlib_syntax.key_option) = let _endpos = _endpos__1_ in
            let _startpos = _startpos__1_ in
            
# 180 "src/lib/smtlib_parser.mly"
                        (mk_data (_startpos,_endpos) Produceassertions )
# 6191 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_key_option _menhir_env _menhir_stack _menhir_s _v _startpos
        | PRODUCEASSIGNEMENT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState3 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__1_ = _endpos in
            let _startpos__1_ = _startpos in
            let _startpos = _startpos__1_ in
            let _v : (Smtlib_syntax.key_option) = let _endpos = _endpos__1_ in
            let _startpos = _startpos__1_ in
            
# 181 "src/lib/smtlib_parser.mly"
                         (mk_data (_startpos,_endpos) Produceassignement )
# 6209 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_key_option _menhir_env _menhir_stack _menhir_s _v _startpos
        | PRODUCEMODELS ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState3 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__1_ = _endpos in
            let _startpos__1_ = _startpos in
            let _startpos = _startpos__1_ in
            let _v : (Smtlib_syntax.key_option) = let _endpos = _endpos__1_ in
            let _startpos = _startpos__1_ in
            
# 182 "src/lib/smtlib_parser.mly"
                    (mk_data (_startpos,_endpos) Producemodels )
# 6227 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_key_option _menhir_env _menhir_stack _menhir_s _v _startpos
        | PRODUCEPROOFS ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState3 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__1_ = _endpos in
            let _startpos__1_ = _startpos in
            let _startpos = _startpos__1_ in
            let _v : (Smtlib_syntax.key_option) = let _endpos = _endpos__1_ in
            let _startpos = _startpos__1_ in
            
# 183 "src/lib/smtlib_parser.mly"
                    (mk_data (_startpos,_endpos) Produceproofs )
# 6245 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_key_option _menhir_env _menhir_stack _menhir_s _v _startpos
        | PRODUCEUNSATASSUMPTIONS ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState3 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__1_ = _endpos in
            let _startpos__1_ = _startpos in
            let _startpos = _startpos__1_ in
            let _v : (Smtlib_syntax.key_option) = let _endpos = _endpos__1_ in
            let _startpos = _startpos__1_ in
            
# 185 "src/lib/smtlib_parser.mly"
      (mk_data (_startpos,_endpos) Produceunsatassumptions )
# 6263 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_key_option _menhir_env _menhir_stack _menhir_s _v _startpos
        | PRODUCEUNSATCORES ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState3 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__1_ = _endpos in
            let _startpos__1_ = _startpos in
            let _startpos = _startpos__1_ in
            let _v : (Smtlib_syntax.key_option) = let _endpos = _endpos__1_ in
            let _startpos = _startpos__1_ in
            
# 186 "src/lib/smtlib_parser.mly"
                        (mk_data (_startpos,_endpos) Produceunsatcores )
# 6281 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_key_option _menhir_env _menhir_stack _menhir_s _v _startpos
        | RANDOMSEED ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState3 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__1_ = _endpos in
            let _startpos__1_ = _startpos in
            let _startpos = _startpos__1_ in
            let _v : (Smtlib_syntax.key_option) = let _endpos = _endpos__1_ in
            let _startpos = _startpos__1_ in
            
# 187 "src/lib/smtlib_parser.mly"
                 (mk_data (_startpos,_endpos) Randomseed )
# 6299 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_key_option _menhir_env _menhir_stack _menhir_s _v _startpos
        | REASONUNKNOWN ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | REGULAROUTPUTCHAN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState3 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__1_ = _endpos in
            let _startpos__1_ = _startpos in
            let _startpos = _startpos__1_ in
            let _v : (Smtlib_syntax.key_option) = let _endpos = _endpos__1_ in
            let _startpos = _startpos__1_ in
            
# 188 "src/lib/smtlib_parser.mly"
                        (mk_data (_startpos,_endpos) Regularoutputchan )
# 6319 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_key_option _menhir_env _menhir_stack _menhir_s _v _startpos
        | RESSOURCELIMIT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState3 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__1_ = _endpos in
            let _startpos__1_ = _startpos in
            let _startpos = _startpos__1_ in
            let _v : (Smtlib_syntax.key_option) = let _endpos = _endpos__1_ in
            let _startpos = _startpos__1_ in
            
# 190 "src/lib/smtlib_parser.mly"
                     (mk_data (_startpos,_endpos) Ressourcelimit )
# 6337 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_key_option _menhir_env _menhir_stack _menhir_s _v _startpos
        | SERIES ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SMTLIBVERSION ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SORTS ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SORTSDESCRIPTION ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | SOURCE ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | STATUTS ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | THEORIES ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | VALUES ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | VERBOSITY ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_lexbuf.Lexing.lex_curr_p in
            let _menhir_s = MenhirState3 in
            let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__1_ = _endpos in
            let _startpos__1_ = _startpos in
            let _startpos = _startpos__1_ in
            let _v : (Smtlib_syntax.key_option) = let _endpos = _endpos__1_ in
            let _startpos = _startpos__1_ in
            
# 189 "src/lib/smtlib_parser.mly"
                (mk_data (_startpos,_endpos) Verbosity )
# 6371 "src/lib/smtlib_parser.ml"
             in
            _menhir_goto_key_option _menhir_env _menhir_stack _menhir_s _v _startpos
        | VERSION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState3 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState3)
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState1 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState1

and _menhir_run372 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (Smtlib_syntax.commands) = 
# 342 "src/lib/smtlib_parser.mly"
                       ( [] )
# 6393 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_commands _menhir_env _menhir_stack _menhir_s _v

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState380 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState378 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState376 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState374 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState369 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState366 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState363 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState357 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState355 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState353 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState352 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState345 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState341 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState340 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState339 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState332 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState330 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState328 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState327 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState326 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState323 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState322 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState320 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState313 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState306 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState303 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState302 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState301 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState300 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState299 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, _), _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState296 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState294 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState293 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, _), _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState289 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState285 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState284 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState279 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState275 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState272 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState271 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, _), _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState268 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState266 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState264 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState260 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState257 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState256 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState253 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState252 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState250 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState246 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, _), _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState240 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState236 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState233 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState232 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, _), _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState229 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState227 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState225 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState224 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState220 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState217 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState216 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _, _menhir_s, _, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState214 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState202 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState197 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState185 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState183 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState175 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState174 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState172 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState171 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState168 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState162 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState159 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState155 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState154 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState147 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState144 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState140 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState130 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState129 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState128 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState127 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState126 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState125 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState123 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState113 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState108 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState104 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState103 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState101 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState96 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState95 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState94 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState93 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState79 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState76 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState58 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState51 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState1 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run2 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 6864 "src/lib/smtlib_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let (_1 : (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 6873 "src/lib/smtlib_parser.ml"
    )) = _v in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.symbol) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 74 "src/lib/smtlib_parser.mly"
               ( mk_data (_startpos,_endpos) (_1) )
# 6883 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_symbol _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run56 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 6890 "src/lib/smtlib_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let (_1 : (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 6899 "src/lib/smtlib_parser.ml"
    )) = _v in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.constant) = 
# 69 "src/lib/smtlib_parser.mly"
                  ( Const_Str _1 )
# 6907 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_constant _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run57 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 6914 "src/lib/smtlib_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let (_1 : (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 6923 "src/lib/smtlib_parser.ml"
    )) = _v in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.constant) = 
# 68 "src/lib/smtlib_parser.mly"
                  ( Const_Num _1 )
# 6931 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_constant _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run94 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AS ->
        _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState94 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | EXCLIMATIONPT ->
        _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | EXISTS ->
        _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | FORALL ->
        _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | LET ->
        _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | LP ->
        _menhir_run125 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | MATCH ->
        _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState94
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState94 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | UNDERSCORE ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState94 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState94

and _menhir_run60 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 6969 "src/lib/smtlib_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let (_1 : (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 6978 "src/lib/smtlib_parser.ml"
    )) = _v in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.constant) = 
# 70 "src/lib/smtlib_parser.mly"
                  ( Const_Hex _1 )
# 6986 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_constant _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run61 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 6993 "src/lib/smtlib_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let (_1 : (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 7002 "src/lib/smtlib_parser.ml"
    )) = _v in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.constant) = 
# 67 "src/lib/smtlib_parser.mly"
                  ( Const_Dec _1 )
# 7010 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_constant _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run62 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 7017 "src/lib/smtlib_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let (_1 : (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 7026 "src/lib/smtlib_parser.ml"
    )) = _v in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.constant) = 
# 71 "src/lib/smtlib_parser.mly"
                  ( Const_Bin _1 )
# 7034 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_constant _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

and _menhir_run9 : _menhir_env -> 'ttv_tail -> Lexing.position -> _menhir_state -> (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 7041 "src/lib/smtlib_parser.ml"
) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _endpos _menhir_s _v _startpos ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _endpos__1_ = _endpos in
    let (_1 : (
# 41 "src/lib/smtlib_parser.mly"
       (string)
# 7050 "src/lib/smtlib_parser.ml"
    )) = _v in
    let _startpos__1_ = _startpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Smtlib_syntax.symbol) = let _endpos = _endpos__1_ in
    let _startpos = _startpos__1_ in
    
# 75 "src/lib/smtlib_parser.mly"
               ( mk_data (_startpos,_endpos) (_1) )
# 7060 "src/lib/smtlib_parser.ml"
     in
    _menhir_goto_symbol _menhir_env _menhir_stack _endpos _menhir_s _v _startpos

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

and commands : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Smtlib_syntax.commands) =
  fun lexer lexbuf ->
    let _menhir_env = {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = Obj.magic ();
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EOF ->
        _menhir_run372 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LP ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)

and term : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Smtlib_syntax.term) =
  fun lexer lexbuf ->
    let _menhir_env = {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = Obj.magic ();
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState376 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | BINARY _v ->
        _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState376 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DECIMAL _v ->
        _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState376 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | HEXADECIMAL _v ->
        _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState376 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LP ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState376 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUMERAL _v ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState376 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRINGLIT _v ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState376 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState376 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState376)

and term_list : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Smtlib_syntax.term list * bool) =
  fun lexer lexbuf ->
    let _menhir_env = {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = Obj.magic ();
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASCIIWOR _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState378 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | BINARY _v ->
        _menhir_run62 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState378 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | DECIMAL _v ->
        _menhir_run61 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState378 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | HEXADECIMAL _v ->
        _menhir_run60 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState378 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | LP ->
        _menhir_run94 _menhir_env (Obj.magic _menhir_stack) MenhirState378 _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | NUMERAL _v ->
        _menhir_run57 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState378 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | STRINGLIT _v ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState378 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | SYMBOL _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) _menhir_env._menhir_lexbuf.Lexing.lex_curr_p MenhirState378 _v _menhir_env._menhir_lexbuf.Lexing.lex_start_p
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState378)

# 345 "src/lib/smtlib_parser.mly"
  

# 7166 "src/lib/smtlib_parser.ml"

# 269 "<standard.mly>"
  

# 7171 "src/lib/smtlib_parser.ml"
