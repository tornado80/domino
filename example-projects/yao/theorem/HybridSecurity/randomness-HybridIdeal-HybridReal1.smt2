;; Key-generation coins always occur at offset zero. These helpers describe
;; the package-instance changes made when one whole wire layer moves between a
;; flat Keys package and LayeredKeys.
(define-fun same-layered-key-coin
    ((l SampleId) (r SampleId) (lo Int) (ro Int)) Bool
    (and (= l r)
         (or (= l (sample-id "LayeredKeys" "GenerateWireKeys" "key_true"))
             (= l (sample-id "LayeredKeys" "GenerateWireKeys" "key_false")))
         (= lo 0) (= ro 0)))

(define-fun top-to-layered-key-coin
    ((l SampleId) (r SampleId) (lo Int) (ro Int)) Bool
    (and
        (or
            (and (= l (sample-id "KeysTop" "GenerateWireKeys" "key_true"))
                 (= r (sample-id "LayeredKeys" "GenerateWireKeys" "key_true")))
            (and (= l (sample-id "KeysTop" "GenerateWireKeys" "key_false"))
                 (= r (sample-id "LayeredKeys" "GenerateWireKeys" "key_false"))))
        (= lo 0) (= ro 0)))

(define-fun layered-to-top-key-coin
    ((l SampleId) (r SampleId) (lo Int) (ro Int)) Bool
    (and
        (or
            (and (= l (sample-id "LayeredKeys" "GenerateWireKeys" "key_true"))
                 (= r (sample-id "KeysTop" "GenerateWireKeys" "key_true")))
            (and (= l (sample-id "LayeredKeys" "GenerateWireKeys" "key_false"))
                 (= r (sample-id "KeysTop" "GenerateWireKeys" "key_false"))))
        (= lo 0) (= ro 0)))

(define-fun layered-to-bot-key-coin
    ((l SampleId) (r SampleId) (lo Int) (ro Int)) Bool
    (and
        (or
            (and (= l (sample-id "LayeredKeys" "GenerateWireKeys" "key_true"))
                 (= r (sample-id "KeysBot" "GenerateWireKeys" "key_true")))
            (and (= l (sample-id "LayeredKeys" "GenerateWireKeys" "key_false"))
                 (= r (sample-id "KeysBot" "GenerateWireKeys" "key_false"))))
        (= lo 0) (= ro 0)))

(define-fun bot-to-layered-key-coin
    ((l SampleId) (r SampleId) (lo Int) (ro Int)) Bool
    (and
        (or
            (and (= l (sample-id "KeysBot" "GenerateWireKeys" "key_true"))
                 (= r (sample-id "LayeredKeys" "GenerateWireKeys" "key_true")))
            (and (= l (sample-id "KeysBot" "GenerateWireKeys" "key_false"))
                 (= r (sample-id "LayeredKeys" "GenerateWireKeys" "key_false"))))
        (= lo 0) (= ro 0)))

(define-fun bot-to-top-key-coin
    ((l SampleId) (r SampleId) (lo Int) (ro Int)) Bool
    (and
        (or
            (and (= l (sample-id "KeysBot" "GenerateWireKeys" "key_true"))
                 (= r (sample-id "KeysTop" "GenerateWireKeys" "key_true")))
            (and (= l (sample-id "KeysBot" "GenerateWireKeys" "key_false"))
                 (= r (sample-id "KeysTop" "GenerateWireKeys" "key_false"))))
        (= lo 0) (= ro 0)))

(define-fun same-layered-sim-coin
    ((l SampleId) (r SampleId) (lo Int) (ro Int)) Bool
    (and (= l r)
         (or
             (= l (sample-id "LayeredSim" "SimulateGarbledGate" "rin_active"))
             (= l (sample-id "LayeredSim" "SimulateGarbledGate" "rout_active"))
             (= l (sample-id "LayeredSim" "SimulateGarbledGate" "rin_inactive"))
             (= l (sample-id "LayeredSim" "SimulateGarbledGate" "rout_inactive"))
             (= l (sample-id "LayeredSim" "SimulateGarbledGate" "rout_zero_0"))
             (= l (sample-id "LayeredSim" "SimulateGarbledGate" "rout_zero_1")))
         (= lo 0) (= ro 0)))

(define-fun sim-to-layered-sim-coin
    ((l SampleId) (r SampleId) (lo Int) (ro Int)) Bool
    (and
        (or
            (and (= l (sample-id "Sim" "SimulateGarbledGate" "rin_active"))
                 (= r (sample-id "LayeredSim" "SimulateGarbledGate" "rin_active")))
            (and (= l (sample-id "Sim" "SimulateGarbledGate" "rout_active"))
                 (= r (sample-id "LayeredSim" "SimulateGarbledGate" "rout_active")))
            (and (= l (sample-id "Sim" "SimulateGarbledGate" "rin_inactive"))
                 (= r (sample-id "LayeredSim" "SimulateGarbledGate" "rin_inactive")))
            (and (= l (sample-id "Sim" "SimulateGarbledGate" "rout_inactive"))
                 (= r (sample-id "LayeredSim" "SimulateGarbledGate" "rout_inactive")))
            (and (= l (sample-id "Sim" "SimulateGarbledGate" "rout_zero_0"))
                 (= r (sample-id "LayeredSim" "SimulateGarbledGate" "rout_zero_0")))
            (and (= l (sample-id "Sim" "SimulateGarbledGate" "rout_zero_1"))
                 (= r (sample-id "LayeredSim" "SimulateGarbledGate" "rout_zero_1"))))
        (= lo 0) (= ro 0)))

(define-fun same-layered-enc-coin
    ((l SampleId) (r SampleId) (lo Int) (ro Int)) Bool
    (and (= l r)
         (or (= l (sample-id "LayeredEnc0" "EncInner" "r"))
             (= l (sample-id "LayeredEnc0" "EncOuter" "r")))
         (= lo ro)))

(define-fun layered-to-flat-enc-coin
    ((l SampleId) (r SampleId) (lo Int) (ro Int)) Bool
    (and
        (or
            (and (= l (sample-id "LayeredEnc0" "EncInner" "r"))
                 (= r (sample-id "Enc" "EncInner" "r")))
            (and (= l (sample-id "LayeredEnc0" "EncOuter" "r"))
                 (= r (sample-id "Enc" "EncOuter" "r"))))
        (= lo ro)))

(define-fun randomness-mapping-GenerateInputWireKeys
    ((l SampleId) (r SampleId) (lo Int) (ro Int)) Bool
    (let ((h (<theorem-consts-HybridSecurity-hybrid$loop> <<theorem-consts>>)))
        (or
            (and (< h 0) (same-layered-key-coin l r lo ro))
            (and (= h 0) (layered-to-top-key-coin l r lo ro))
            (and (= h 1) (top-to-layered-key-coin l r lo ro))
            (and (> h 1) (same-layered-key-coin l r lo ro)))))

(define-fun randomness-mapping-GarbleGate
    ((l SampleId) (r SampleId) (lo Int) (ro Int)) Bool
    (let ((h (<theorem-consts-HybridSecurity-hybrid$loop> <<theorem-consts>>))
          (d (<theorem-consts-HybridSecurity-d> <<theorem-consts>>))
          (layer <arg-HybridIdeal-GarbleGate-layer>))
        (or
            ;; Before the hybrid range both games garble every valid layer.
            (and (< h 0)
                 (or (same-layered-key-coin l r lo ro)
                     (same-layered-enc-coin l r lo ro)))

            ;; Initial bridge: all-real on the left, layer 1 split out on the
            ;; right, then ordinary real layers on both sides.
            (and (> d 0) (= h 0) (= layer 1)
                 (or (layered-to-bot-key-coin l r lo ro)
                     (layered-to-flat-enc-coin l r lo ro)))
            (and (> d 0) (= h 0) (> layer 1)
                 (or (same-layered-key-coin l r lo ro)
                     (same-layered-enc-coin l r lo ro)))

            ;; Interior bridge.
            (and (> h 0) (< h d) (< layer (- h 1))
                 (or (same-layered-key-coin l r lo ro)
                     (same-layered-sim-coin l r lo ro)))
            (and (> h 0) (< h d) (= layer (- h 1))
                 (or (top-to-layered-key-coin l r lo ro)
                     (same-layered-sim-coin l r lo ro)))
            (and (> h 0) (< h d) (= layer h)
                 (or (bot-to-top-key-coin l r lo ro)
                     (sim-to-layered-sim-coin l r lo ro)))
            (and (> h 0) (< h d) (= layer (+ h 1))
                 (or (layered-to-bot-key-coin l r lo ro)
                     (layered-to-flat-enc-coin l r lo ro)))
            (and (> h 0) (< h d) (> layer (+ h 1))
                 (or (same-layered-key-coin l r lo ro)
                     (same-layered-enc-coin l r lo ro)))

            ;; Final bridge: common simulated prefix, then the left ideal
            ;; assumption versus the final right simulated layer.
            (and (> d 0) (= h d) (< layer (- h 1))
                 (or (same-layered-key-coin l r lo ro)
                     (same-layered-sim-coin l r lo ro)))
            (and (> d 0) (= h d) (= layer (- h 1))
                 (or (top-to-layered-key-coin l r lo ro)
                     (same-layered-sim-coin l r lo ro)))
            (and (> d 0) (= h d) (= layer h)
                 (or (bot-to-layered-key-coin l r lo ro)
                     (sim-to-layered-sim-coin l r lo ro)))

            ;; After the hybrid range both games simulate every valid layer.
            (and (> d 0) (> h d)
                 (or (same-layered-key-coin l r lo ro)
                     (same-layered-sim-coin l r lo ro))))))
