###############
## SUM TYPES ##
###############

Test 1.1 : option refine

  $ $MERLIN single case-analysis -start 4:9 -end 4:10 -filename refine_patternre.ml <<EOF \
  > let _ = \
  >   match (None : unit option) with \
  >   | None -> () \
  >   | Some _ -> () \
  > EOF
  {
    "class": "return",
    "value": [
      {
        "start": {
          "line": 4,
          "col": 9
        },
        "end": {
          "line": 4,
          "col": 10
        }
      },
      "()"
    ],
    "notifications": []
  }

Test 1.2 : option refine

  $ cat >typ12re.ml <<EOF \
  > type t = A | B of int \
  > let _ = \
  >   match (None : t option) with \
  >   | None -> () \
  >   | Some _ -> () \
  > EOF

  $ $MERLIN single case-analysis -start 5:9 -end 5:10 -filename typ12re.ml < typ12re.ml \
  > sed -e 's/, /,/g' | sed -e 's/ *| */|/g' | tr -d '\n' | jq '.'
  {
    "class": "return",
    "value": [
      {
        "start": {
          "line": 5,
          "col": 4
        },
        "end": {
          "line": 5,
          "col": 10
        }
      },
      "Some (A)|Some (B _)"
    ],
    "notifications": []
  }

Test 1.3 : FIXME ? int option

  $ cat >typ13re.ml <<EOF \
  > let _ = \
  >   match (None : int option) with \
  >   | None -> () \
  >   | Some _ -> () \
  > EOF

  $ $MERLIN single case-analysis -start 4:9 -end 4:10 -filename typ13re.ml < typ13re.ml \
  > sed -e 's/, /,/g' | sed -e 's/ *| */|/g' | tr -d '\n' | jq '.'
  {
    "class": "return",
    "value": [
      {
        "start": {
          "line": 4,
          "col": 4
        },
        "end": {
          "line": 4,
          "col": 10
        }
      },
      "Some 0|Some _"
    ],
    "notifications": []
  }

#############
## RECORDS ##
#############

Test 2.1

  $ cat >typ4rere.ml <<EOF \
  > type b = C | D of string \
  > type a = A | B of b   \
  > type recd = { a : a } \
  > let f (x : recd) =    \
  >   match x with        \
  >   | { a = A } -> ()   \
  >   | { a = B _ } -> () \
  > EOF

  $ $MERLIN single case-analysis -start 7:12 -end 7:12 -filename typ4rere.ml <typ4rere.ml | \
  > sed -e 's/ *| */|/g' | tr -d '\n' | jq '.'
  {
    "class": "return",
    "value": [
      {
        "start": {
          "line": 7,
          "col": 4
        },
        "end": {
          "line": 7,
          "col": 15
        }
      },
      "{ a = B (C) }|{ a = B (D _) }"
    ],
    "notifications": []
  }

Test 2.2

  $ cat >typ4bre.ml <<EOF                       \
  > type a = A | B                            \
  > type recd = { x : a; y : bool; z : a }    \
  > let f (r : recd) =                        \
  >   match r with                            \
  >   | { x = _ ; y ; _ } -> ()           \
  > EOF

  $ $MERLIN single case-analysis -start 5:11 -end 5:11 -filename typ4bre.ml <typ4bre.ml | \
  > sed -e 's/ *| */|/g' | tr -d '\n' | jq '.'
  {
    "class": "return",
    "value": [
      {
        "start": {
          "line": 5,
          "col": 4
        },
        "end": {
          "line": 5,
          "col": 21
        }
      },
      "{ x = A; y;_}|{ x = B; y;_}"
    ],
    "notifications": []
  }

##########################
## POLYMORPHIC VARIANTS ##
##########################

Test 3.1

  $ cat >typ2re.ml <<EOF \
  > type blues = [ \`Cyan | \`Methyl ] \
  > type basic_color = [ \`Blue of blues ] \
  > let f (x : basic_color) = \
  >   match x with          \
  >   | \`Blue _ -> ()        \
  > EOF

  $ $MERLIN single case-analysis -start 5:11 -end 5:11 -filename typ2re.ml <typ2re.ml | \
  > sed -e 's/ *| */|/g' | tr -d '\n' | jq '.'
  {
    "class": "return",
    "value": [
      {
        "start": {
          "line": 5,
          "col": 4
        },
        "end": {
          "line": 5,
          "col": 11
        }
      },
      "`Blue `Methyl|`Blue `Cyan"
    ],
    "notifications": []
  }

##########
## GADT ##
##########

Test 4.1 : Fixme: missing space and ()

  $ cat >typ3re.ml <<EOF                              \
  > type _ sub_t =                                  \
  >   | A : int -> int sub_t                        \
  >   | B : int -> float sub_t                      \
  > type _ term =                                   \
  >  | Int : int sub_t -> int term                  \
  > let eval : type a. a term -> a term =           \
  >   fun x : a term -> match x with                \
  >   | Int _ -> ()                                 \
  > EOF

  $ $MERLIN single case-analysis -start 8:8 -end 8:8 -filename typ3re.ml <typ3re.ml | \
  > sed -e 's/, /,/g' | sed -e 's/ *| */|/g' | tr -d '\n' | jq '.'
  {
    "class": "return",
    "value": [
      {
        "start": {
          "line": 8,
          "col": 8
        },
        "end": {
          "line": 8,
          "col": 9
        }
      },
      "A_"
    ],
    "notifications": []
  }

Test 4.2

  $ cat >typ3bre.ml <<EOF                             \
  > type _ sub_t =                                  \
  >   | A : int -> int sub_t                        \
  >   | B : int -> int sub_t                        \
  > type _ term =                                   \
  >  | Int : int sub_t -> int term                  \
  > let eval : type a. a term -> a term =           \
  >   fun x : a term -> match x with                \
  >   | Int _ -> ()                                 \
  > EOF

  $ $MERLIN single case-analysis -start 8:8 -end 8:8 -filename typ3bre.ml <typ3bre.ml | \
  > sed -e 's/, /,/g' | sed -e 's/ *| */|/g' | tr -d '\n' | jq '.'
  {
    "class": "return",
    "value": [
      {
        "start": {
          "line": 8,
          "col": 4
        },
        "end": {
          "line": 8,
          "col": 9
        }
      },
      "Int (A _)|Int (B _)"
    ],
    "notifications": []
  }

############
## ERRORS ##
############

Test 5.1 : Nothing to do

  $ $MERLIN single case-analysis -start 4:9 -end 4:11 -filename nothing_to_dore.ml <<EOF \
  > let _ = \
  >   match (None : unit option) with \
  >   | None -> () \
  >   | Some () -> () \
  > EOF
  {
    "class": "error",
    "value": "Nothing to do",
    "notifications": []
  }
