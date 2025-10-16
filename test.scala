import stainless.lang.*
//import stainless.collection.*
import stainless.annotation.*

//trait Res
@noEq
case class Box[T](t: T)


//case class Err() extends Res
@noEq
def foo [T](t: T): T = {
  t
}

//def mirror[T]() = {
//  (t, t)
//}.ensuring(_ => t == t)

def test() = {
  foo(1.0)
  assert(foo(1.0) == foo(1.0))
}

def test2() = {
  Box(1.0)
}