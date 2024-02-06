(module
    (table 4 funcref)

    (type $clos
        (struct
            (field $func_pointer i32)
            (field $env anyref)))
    (type $i32box
        (struct
            (field $value i32)))
    (type $generic-type (func (param anyref) (param anyref) (result anyref)))
    (type $maketwice-env
        (struct))
    (type $twice-env
        (struct
            (field $f (ref $clos))))
    (type $makeadd-env
        (struct))
    (type $add-env
        (struct
            (field $x (ref $i32box))))

    (func $box (param $x i32) (result (ref $i32box))
            (struct.new $i32box
            (local.get $x)))

    (func $unbox (param $box (ref $i32box)) (result i32)
            (struct.get $i32box $value
            (local.get $box)))

    (func $maketwice (param $arg0 anyref) (param $arg1 anyref) (result anyref)
        (local $env (ref $maketwice-env))
        (local $f (ref $clos))
            (local.set $env
            (ref.cast
                (ref $maketwice-env)
                (local.get $arg0)))
        (local.set $f
            (ref.cast
                (ref $clos)
                (local.get $arg1)))
        (struct.new $clos
            (i32.const 1)
            (struct.new $twice-env
                (local.get $f))))

    (func $twice (param $arg0 anyref) (param $arg1 anyref) (result anyref)
        (local $env (ref $twice-env))
        (local $x (ref $i32box))
            (local.set $env
            (ref.cast
                (ref $twice-env)
                (local.get $arg0)))
        (local.set $x
            (ref.cast
                (ref $i32box)
                (local.get $arg1)))
        (call $apply
            (struct.get $twice-env $f
                (ref.cast
                    (ref $twice-env)
                    (local.get $env)))
            (call $apply
                (struct.get $twice-env $f
                    (ref.cast
                        (ref $twice-env)
                        (local.get $env)))
                (local.get $x))))

    (func $makeadd (param $arg0 anyref) (param $arg1 anyref) (result anyref)
        (local $env (ref $makeadd-env))
        (local $x (ref $i32box))
            (local.set $env
            (ref.cast
                (ref $makeadd-env)
                (local.get $arg0)))
        (local.set $x
            (ref.cast
                (ref $i32box)
                (local.get $arg1)))
        (struct.new $clos
            (i32.const 3)
            (struct.new $add-env
                (local.get $x))))

    (func $add (param $arg0 anyref) (param $arg1 anyref) (result anyref)
        (local $env (ref $add-env))
        (local $y (ref $i32box))
            (local.set $env
            (ref.cast
                (ref $add-env)
                (local.get $arg0)))
        (local.set $y
            (ref.cast
                (ref $i32box)
                (local.get $arg1)))
        (call $box
            (i32.add
                (call $unbox
                    (struct.get $add-env $x
                        (ref.cast
                            (ref $add-env)
                            (local.get $env))))
                (call $unbox
                    (local.get $y)))))

    (func $apply (param $cl_uncast anyref) (param $arg anyref) (result anyref)
        (local $cl (ref $clos))
            (local.set $cl
            (ref.cast
                (ref $clos)
                (local.get $cl_uncast)))
        (call_indirect
            (type $generic-type)
            (struct.get $clos $env
                (local.get $cl))
            (local.get $arg)
            (struct.get $clos $func_pointer
                (local.get $cl))))

    (func $mexpr  (result i32)
        (local $result anyref)
            (local.set $result
            (call $apply
                (call $apply
                    (struct.new $clos
                        (i32.const 0)
                        (struct.new $maketwice-env))
                    (call $apply
                        (struct.new $clos
                            (i32.const 2)
                            (struct.new $makeadd-env))
                        (call $box
                            (i32.const 1))))
                (call $box
                    (i32.const 0))))
        (call $unbox
            (ref.cast
                (ref $i32box)
                (local.get $result))))

    (elem (i32.const 0) $maketwice $twice $makeadd $add)
    (export "mexpr" (func $mexpr)))
