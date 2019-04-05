let PList =
      http://prelude.dhall-lang.org/List/package.dhall sha256:ca82b0e91b63a044b425b47a0ac02c3c0e726acf1c8b567cdc24ebac0073209a

let tail
    :  forall(a: Type)
    -> List a
    -> List a
    =  \(a: Type)
    -> \(l: List a)
    -> List/Build
         a
         (   λ(list : Type)
           → λ(cons : a → list → list)
           → λ(nil : list)
           → List/fold a l list (
                \(x: a) ->
                \(p: list) ->
                nil
             ) nil
         )
    List/fold
    
        a
        l
        (List a)
        (    \(x: a)
          -> \(q: List a)
          -> q
        )
        ([] : List a)

in tail Text [ "ABC", "DEF", "GHI" ]
-- let nth
--     :      forall(a : Type)
--         -> Natural
--         -> List a
--         -> Optional a
--     =  \(a: Type)
--     -> \(n: Natural)
--     -> \(l: List a)
--     -> Natural/fold n 
-- 
-- in nth Text 2 [ "ABC", "DEF", "GHI" ]
-- let zip
--     :   ∀(a : Type)
--       → ∀(b : Type)
--       → { _1 : List a, _2 : List b }
--       → List { _1 : a, _2 : b }
--     =   λ(a : Type)
--       → λ(b : Type)
--       → λ(xs : { _1 : List a, _2 : List b })
--       -- → List/build
--       --   { _1 : a, _2 : b }
--       --   (   λ(list : Type)
--       --     → λ(cons : { _1 : a, _2 : b } → list → list)
--       --     → λ(nil : list)
--       --     → List/fold { index : Natural, value : a } (List/indexed a xs._1) list (
--       --           \(x: { index : Natural, value : a }) ->
--       --           \(p: list) ->
--       --           List/fold b xs._2 list (\(y: b) -> \(q: list) -> cons { _1 = x.value, _2 = y } q) nil : list
--       --       ) nil
--       --   )
--       → PList.map { index : Natural, value : a } { index : Natural, value : a } (List/indexed a xs._1) (
--             \(x: { index : Natural, value : a }) ->
--             List/fold b xs._2 list (\(y: b) -> \(q: list) -> cons { _1 = x.value, _2 = y } q) nil : list
--         ) nil
--
-- in  zip Text Bool { _1 = [ "ABC", "DEF", "GHI" ], _2 = [ True, False, True ] }
