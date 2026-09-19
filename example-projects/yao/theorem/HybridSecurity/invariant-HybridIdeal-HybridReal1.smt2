(define-fun optional-wire-layer
    ((table (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
     (empty (Array Int (Maybe (Array Bool (Maybe Bits_n))))))
    (Maybe (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
    (ite (= table empty)
         (as mk-none
             (Maybe (Array Int (Maybe (Array Bool (Maybe Bits_n))))))
         (mk-some table)))

(define-fun optional-active-layer
    ((table (Array Int (Maybe Bool)))
     (empty (Array Int (Maybe Bool))))
    (Maybe (Array Int (Maybe Bool)))
    (ite (= table empty)
         (as mk-none (Maybe (Array Int (Maybe Bool))))
         (mk-some table)))

(define-state-relation invariant
    (left right)
    (let
        ((h (<theorem-consts-HybridSecurity-hybrid$loop> <<theorem-consts>>))
         (d (<theorem-consts-HybridSecurity-d> <<theorem-consts>>))
         (none-wire-layer
             (as mk-none
                 (Maybe (Array Int (Maybe (Array Bool (Maybe Bits_n)))))))
         (none-active-layer
             (as mk-none (Maybe (Array Int (Maybe Bool)))))
         (empty-wire-keys
             ((as const (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
              (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
         (empty-active-bits
             ((as const (Array Int (Maybe Bool)))
              (as mk-none (Maybe Bool)))))
        (or
            ;; With no gate layers, every exported oracle aborts before state
            ;; access. The initial outer tables are equal and remain untouched.
            (and (<= d 0)
                 (= left.LayeredKeys.WireKey right.LayeredKeys.WireKey)
                 (= left.LayeredKeys.ActiveBit right.LayeredKeys.ActiveBit))

            ;; Outside the hybrid range neither KeysFilter redirects a valid
            ;; circuit layer, so both sides use LayeredKeys directly.
            (and (> d 0) (< h 0)
                 (= left.LayeredKeys.WireKey right.LayeredKeys.WireKey)
                 (= left.LayeredKeys.ActiveBit right.LayeredKeys.ActiveBit))
            (and (> d 0) (> h d)
                 (= left.LayeredKeys.WireKey right.LayeredKeys.WireKey)
                 (= left.LayeredKeys.ActiveBit right.LayeredKeys.ActiveBit))

            ;; Initial bridge: HybridIdeal(0) is all-real, while
            ;; HybridReal(1) splits wire layers 1 and 2 out of LayeredKeys.
            (and (> d 0) (= h 0)
                 (= (store
                        (store left.LayeredKeys.WireKey 1 none-wire-layer)
                        2 none-wire-layer)
                    (store
                        (store right.LayeredKeys.WireKey 1 none-wire-layer)
                        2 none-wire-layer))
                 (= (store
                        (store left.LayeredKeys.ActiveBit 1 none-active-layer)
                        2 none-active-layer)
                    (store
                        (store right.LayeredKeys.ActiveBit 1 none-active-layer)
                        2 none-active-layer))
                 (= (select left.LayeredKeys.WireKey 1)
                    (optional-wire-layer right.KeysTop.WireKey empty-wire-keys))
                 (= (select left.LayeredKeys.ActiveBit 1)
                    (optional-active-layer right.KeysTop.ActiveBit empty-active-bits))
                 (= (select left.LayeredKeys.WireKey 2)
                    (optional-wire-layer right.KeysBot.WireKey empty-wire-keys))
                 (= (select left.LayeredKeys.ActiveBit 2)
                    (optional-active-layer right.KeysBot.ActiveBit empty-active-bits)))

            ;; Interior bridge: wire layer h moves from left KeysTop to the
            ;; right nested table, h + 1 moves KeysBot -> KeysTop, and h + 2
            ;; moves from the left nested table to right KeysBot.
            (and (> d 0) (> h 0) (< h d)
                 (= (store
                        (store left.LayeredKeys.WireKey h none-wire-layer)
                        (+ h 2) none-wire-layer)
                    (store
                        (store right.LayeredKeys.WireKey h none-wire-layer)
                        (+ h 2) none-wire-layer))
                 (= (store
                        (store left.LayeredKeys.ActiveBit h none-active-layer)
                        (+ h 2) none-active-layer)
                    (store
                        (store right.LayeredKeys.ActiveBit h none-active-layer)
                        (+ h 2) none-active-layer))
                 (= (select right.LayeredKeys.WireKey h)
                    (optional-wire-layer left.KeysTop.WireKey empty-wire-keys))
                 (= (select right.LayeredKeys.ActiveBit h)
                    (optional-active-layer left.KeysTop.ActiveBit empty-active-bits))
                 (= left.KeysBot.WireKey right.KeysTop.WireKey)
                 (= left.KeysBot.ActiveBit right.KeysTop.ActiveBit)
                 (= (select left.LayeredKeys.WireKey (+ h 2))
                    (optional-wire-layer right.KeysBot.WireKey empty-wire-keys))
                 (= (select left.LayeredKeys.ActiveBit (+ h 2))
                    (optional-active-layer right.KeysBot.ActiveBit empty-active-bits)))

            ;; Final bridge: HybridIdeal(d) splits the last two wire layers;
            ;; HybridReal(d + 1) is all-simulated and stores both nested.
            (and (> d 0) (= h d)
                 (= (store
                        (store left.LayeredKeys.WireKey d none-wire-layer)
                        (+ d 1) none-wire-layer)
                    (store
                        (store right.LayeredKeys.WireKey d none-wire-layer)
                        (+ d 1) none-wire-layer))
                 (= (store
                        (store left.LayeredKeys.ActiveBit d none-active-layer)
                        (+ d 1) none-active-layer)
                    (store
                        (store right.LayeredKeys.ActiveBit d none-active-layer)
                        (+ d 1) none-active-layer))
                 (= (select right.LayeredKeys.WireKey d)
                    (optional-wire-layer left.KeysTop.WireKey empty-wire-keys))
                 (= (select right.LayeredKeys.ActiveBit d)
                    (optional-active-layer left.KeysTop.ActiveBit empty-active-bits))
                 (= (select right.LayeredKeys.WireKey (+ d 1))
                    (optional-wire-layer left.KeysBot.WireKey empty-wire-keys))
                 (= (select right.LayeredKeys.ActiveBit (+ d 1))
                    (optional-active-layer left.KeysBot.ActiveBit empty-active-bits))))))
