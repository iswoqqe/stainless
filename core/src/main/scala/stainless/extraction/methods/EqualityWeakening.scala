/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package methods

import inox.utils.Position

class EqualityWeakening(override val s: Trees, override val t: Trees)
                  (using override val context: inox.Context)
  extends oo.CachingPhase
    with oo.NoSummaryPhase
    with IdentitySorts
    with oo.SimpleTypeDefs { self =>

  override protected type ClassResult    = Option[t.ClassDef]
  override protected type FunctionResult = Option[t.FunDef]


  protected val typeDefCache = new ExtractionCache[s.TypeDef, (t.TypeDef, TypeDefSummary)]({ (td, ctx) =>
    import ctx.symbols
    TypeDefKey(td)
  })


  override protected val classCache = new ExtractionCache[s.ClassDef, (ClassResult, ClassSummary)]({ (cd, ctx) =>
    import ctx.symbols
    ClassKey(cd)
  })

  override protected final val funCache = new ExtractionCache[s.FunDef, (FunctionResult, FunctionSummary)]({ (fd, ctx) =>
    import ctx.symbols
    FunctionKey(fd)
  })

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(self.s, self.t)(using symbols)

  private val genericType = FreshIdentifier("T")
  val weakEq = t.FunDef(
    FreshIdentifier("weakEq"),
    List(t.TypeParameterDef(genericType)),
    List(t.ValDef(FreshIdentifier("lhs"), t.TypeParameter(genericType, List())), t.ValDef(FreshIdentifier("rhs"), t.TypeParameter(genericType, List()))),
    t.BooleanType(),
    t.Choose(t.ValDef(FreshIdentifier("res"), t.BooleanType()), t.BooleanLiteral(true)),
    List()
  )

  private val noEqVars: collection.mutable.Set[Identifier] = collection.mutable.Set()


  private class NoEqTraverserImpl(override val trees: self.s.type) extends oo.TreeTraverser {

    import s._

    override def traverse(fd: FunDef): Unit = {
      if (fd.flags.contains(Annotation("noEq", List()))) {
        fd.tparams.foreach(p => noEqVars.add(p.id))
      }
      super.traverse(fd)
    }

    override def traverse(cd: ClassDef): Unit = {
      if (cd.flags.contains(Annotation("noEq", List()))) {
        cd.tparams.foreach(p => noEqVars.add(p.id))
      }
      super.traverse(cd)
    }
  }

  protected class TransformerContext(override val s: self.s.type, override val t: self.t.type)
                                    (using val symbols: s.Symbols) extends oo.ConcreteTreeTransformer(s, t) {
    import s._
    import symbols._

    private val noEqTraverser = new NoEqTraverserImpl(s)
    symbols.functions.values.foreach(noEqTraverser.traverse)
    symbols.classes.values.foreach(noEqTraverser.traverse)

    override def transform(e: Expr): t.Expr = e match {
      case Equals(lhs, rhs) =>
        lhs.getType match {
          case tp@TypeParameter(id, flags)  =>
            if noEqVars(id) then
             t.FunctionInvocation(weakEq.id, List(t.TypeParameter(id,flags.map(transform))), List(transform(lhs), transform(rhs))).setPos(e)
            else super.transform(e)
          case _ => super.transform(e)
        }

      case _ => super.transform(e)
    }
  }

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): (Option[t.ClassDef], Unit) = {
    (Some(context.transform(cd)), ())
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): (Option[t.FunDef], Unit) = {
    (Some(context.transform(fd)), ())
  }

  override protected def extractTypeDef(context: TransformerContext, td: s.TypeDef): (t.TypeDef, Unit) = {
    (context.transform(td), ())
  }

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Option[t.FunDef]]): t.Symbols =
    symbols.withFunctions(weakEq +: functions.flatten)

  override protected def registerClasses(symbols: t.Symbols, classes: Seq[Option[t.ClassDef]]): t.Symbols =
    symbols.withClasses(classes.flatten)
}

object EqualityWeakening {
  def apply(ts: Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: ts.type
  } = {
    class Impl(override val s: ts.type, override val t: ts.type) extends EqualityWeakening(s, t)
    new Impl(ts, ts)
  }
}
