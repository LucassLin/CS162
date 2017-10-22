import Math._
import scala.swing._
import scala.swing.event._
import java.awt.Color
import java.awt.geom._

// defined in the code below
import Utility._
import Images._
import SpatialTransforms._
import Masking._
import ExampleMask._
import ExampleGray._
import ExampleClr._

//——————————————————————————————————————————————————————————————————————————————
// main entry point

object SaveAll {
  def main(args: Array[String]) {
    Main.saveAllImages("test_images")
  }
}

object Main {
  // example coordinates to use for displaying example images
  val coord = Coord(500, 500, 250, 250, 5, 5)

  // the mask example images, from ExampleMask
  val masks = multiApply((mask: ImgMask) => new ImgMaskGUI(coord, mask),
                         Seq(vstrip,
                             hstrip,
                             checker,
                             altRings,
                             polarChecker,
                             udisk,
                             scaledisk,
                             transdisk,
                             filtscaledisk,
                             filttransdisk,
                             swirled,
                             annulus(0.25),
                             radReg(7),
                             wedgeAnnulus,
                             shifted,
                             rotatedLine(0.33),
                             bigX,
                             asterisk,
                             inverseAsterisk,
                             recordShape,
                             asteriskMinusX))

  // the grayscale example images, from ExampleGray
  val grays = multiApply((gray: ImgGray) => new ImgGrayGUI(coord, gray),
                         Seq(wavDist,
                             grayGradient(coord.imgWidth)))

  // the color example images, from ExampleClr
  val clrs = multiApply((clr: ImgClr) => new ImgClrGUI(coord, clr),
                        Seq(ybRings,
                            colorChecker,
                            lerped,
                            colorVStrip,
                            colorCross,
                            checkerRingStrip,
                            inverseCheckerRingStrip,
                            grayColorGradient(coord.imgWidth),
                            bigXChecker,
                            ringsAsteriskOnChecker))

  val allImages: Map[String, Seq[ImgGUI]] =
    Map("mask" -> masks,
        "gray" -> grays,
        "color" -> clrs)

  def saveAllImages(toDir: String) {
    allImages.values.foreach(images => {
      images.zip(0.until(images.size)).foreach(
        { case (image, id) => image.save(toDir, id.toString) })
    })
  }

  def multiApply[A, B](f: A => B, args: Seq[A]): Seq[B] = {
    args.map(f)
  }

  // the first command-line argument <mask|gray|clr> says whether
  // we're displaying an image from masks, grays, or clrs. the
  // second argument <index> specifies an index into the appropriate
  // list for the image to display. the optional third argument
  // [save], if present, says to save the resulting image into a PNG
  // file named <mask|gray|clr><index>.png.
  def usage() {
    println("usage: scala Main <mask|gray|clr> <index> [save]\nexample: scala Main mask 11 save")
  }

  // this program takes command-line options to determine what image
  // to display on the screen out of a predefined list of example
  // images. the command-line usage for this program is explained in
  // the comments below. see the comments in the GUI code at the
  // bottom of the file for explanations of Coord, ImgMaskGUI,
  // ImgGrayGUI, and ImgClrGUI.
  def main(args: Array[String]) {
    // parse the command line and display the appropriate image
    // check number of command-line arguments
    if (args.length < 2 || args.length > 3) {
      usage()
      sys.exit(1)
    }

    // try to get the image index; it should be a number
    val idx =
      try {
        args(1).toInt
      } catch {
        case _: NumberFormatException => {
          println(usage)
          sys.exit(1)
        }
      }

    // determine whether we're displaying one of the mask, grayscale,
    // or color images and display the appropriate one based on the
    // given index
    allImages.get(args(0)) match {
      case Some(images) => {
        if (idx >= images.length) {
          println("there are only " + images.length + " " + args(0) + " images")
          sys.exit(1)
        } else {
          val img = images(idx)
          img.show()
          if (args.length == 3 && args(2) == "save") {
            img.save(".", idx.toString)
          }
        }
      }
      case None => {
        usage()
        sys.exit(1)
      }
    }
  } // main
} // Main


//——————————————————————————————————————————————————————————————————————————————
// Example images that exercise the image DSL. see the 'Functional
// Images' section of the code below to see the definitions of
// the types used here.

// example mask image definitions
object ExampleMask {
  val vstrip: ImgMask =
    pt => abs(pt.x) <= 0.5

  val hstrip: ImgMask =
    pt => abs(pt.y) <= 0.5

  val checker: ImgMask =
    pt => (floor(pt.x) + floor(pt.y)).toInt % 2 == 0

  val altRings: ImgMask =
    pt => floor(dist(pt)).toInt % 2 == 0

  val polarChecker: ImgMask = {
    val sc = (plr: Polar) => Point(plr.rho, plr.theta * (10/PI))
    checker compose sc compose pt2plr
  }

  val udisk: ImgMask =
    pt => dist(pt) < 1

  val scaledisk: ImgMask =
    udisk compose scalePt(Vector(2,2))

  val transdisk: ImgMask =
    udisk compose translatePt(Vector(1,0))

  val filtscaledisk: ImgMask =
    scale(Vector(2,2))(udisk)

  val filttransdisk: ImgMask =
    translate(Vector(1,0))(udisk)

  val swirled: ImgMask =
    swirl(1)(vstrip)

  val annulus: Value => ImgMask =
    sc => diffM(udisk)(scale(Vector(sc,sc))(udisk))

  val radReg: Int => ImgMask =
    n => {
      val test = (plr: Polar) => floor(plr.theta * (n/PI)).toInt % 2 == 0
      test compose pt2plr
    }

  val wedgeAnnulus: ImgMask =
    intersectM(annulus(0.25))(radReg(7))

  val shiftXor: Value => FiltMask =
    dx => img => xorM(
      translate(Vector(dx,0))(img))(
      translate(Vector(-dx,0))(img)
    )

  val shifted: ImgMask =
    shiftXor(2.6)(altRings)

  val rotatedLine: Double => ImgMask =
    amount => rotate(amount)(vstrip)

  val bigX: ImgMask =
    unionM(rotatedLine(0.45))(rotatedLine(-0.45))

  val asterisk: ImgMask =
    unionM(unionM(vstrip)(rotatedLine(-0.90)))(rotatedLine(0.90))

  val inverseAsterisk: ImgMask =
    xorM(asterisk)(fullM)

  val recordShape: ImgMask = {
    val fun = (plr: Polar) => Polar(math.abs(plr.rho - 1.5), plr.theta)
    udisk compose polarXf(fun)
  }

  val asteriskMinusX: ImgMask =
    diffM(diffM(asterisk)(bigX))(emptyM)
}

// example grayscale image definitions
object ExampleGray {
  val wavDist: ImgGray =
    pt => (1 + cos(PI * dist(pt))) / 2

  val grayGradient: Double => ImgGray =
    width => pt => math.abs(pt.x) / width
}

// example color image definitions
object ExampleClr {
  // various colors
  val invisible = Colour(0, 0, 0, 0)
  val black = Colour(0, 0, 0, 1)
  val white = Colour(1, 1, 1, 1)
  val red = Colour(1, 0, 0, 1)
  val green = Colour(0, 1, 0, 1)
  val blue = Colour(0, 0, 1, 1)
  val yellow = Colour(1, 1, 0, 1)

  // translate a mask into a colour image, translating true and false
  // values in the mask into the given respective colors
  val maskAsColors: ImgMask => Colour => Colour => ImgClr =
    mask => ifTrue => ifFalse => selectImgClr(mask)(lift0(ifTrue))(lift0(ifFalse))

  val ybRings: ImgClr =
    lerpImgClr(wavDist)(lift0(blue))(lift0(yellow))

  val colorChecker: ImgClr =
    maskAsColors(checker)(black)(white)

  val lerped: ImgClr =
    lerpImgClr(wavDist)(
      maskAsColors(checker)(black)(white))(
      maskAsColors(polarChecker)(blue)(yellow))

  val colorVStrip: ImgClr =
    msk2clr(vstrip)

  val colorCross: ImgClr =
    overlayImgClr(
      maskAsColors(vstrip)(black)(invisible))(
      maskAsColors(hstrip)(red)(invisible))

  val checkerRingStrip: ImgClr =
    selectImgClr(vstrip)(ybRings)(colorChecker)

  val inverseCheckerRingStrip: ImgClr =
    selectImgClr(notM(vstrip))(ybRings)(colorChecker)

  val grayColorGradient: Double => ImgClr =
    width => gray2clr(grayGradient(width))

  val bigXChecker: ImgClr =
    selectImgClr(bigX)(colorChecker)(lift0(green))

  val ringsAsteriskOnChecker: ImgClr =
    selectImgClr(asterisk)(ybRings)(colorChecker)
}


//——————————————————————————————————————————————————————————————————————————————
// Functional Images
//
// An image is defined as a function from a cartesian coordinate Point
// (defined below) to some value; we specifically use three kinds of
// values: Booleans (yielding a black-and-white image), Doubles
// (yielding a grayscale image), and Colours (defined below, yielding
// a color image).
//
// NOTE 1: the comments specifying what to implement below use
// 'method' to mean defining a function using the 'def' keyword and
// 'function' to mean defining a function using the 'val'
// keyword. recall that, semantically, methods and functions are not
// quite the same thing.
//
// NOTE 2: often the Scala compiler will be able to figure out all of
// the necessary types automatically, but sometimes it will not and
// you will need to give them manually. we suggest that you first
// implement things without explicit type annotations, and then add
// them in later if the compiler complains. of course, this note
// doesn't apply to generic types using type variables which must
// always be explicitly declared.
//
// NOTE 3: in our solution, the bodies of all of the functions you are
// supposed to define are only a single line long. if your solutions
// are more than that, you are probably doing something wrong (or at
// least in a more complicated way than necessary).

// a point in the cartesian coordinate system
case class Point(x: Double, y: Double)

// a point in the polar coordinate system
case class Polar(rho: Double, theta: Double)

// Colours (using the British spelling to distinguish from the
// existing java.awt.Color) are defined as four values: Red, Green,
// Blue, and alpha (the color's transparency).
case class Colour(R: Value, G: Value, B: Value, alpha: Value)

// a vector
case class Vector(x: Double, y: Double) {
  def neg = Vector(-x, -y)
  def inverse = Vector(1/x, 1/y)
}

// some useful utility functions
object Utility {
  // compute distance from origin
  def dist(pt: Point): Double =
    sqrt(pow(pt.x, 2) + pow(pt.y, 2))

  // transform cartesian to polar coordinates
  def pt2plr(pt: Point): Polar =
    Polar(dist(pt), atan2(pt.y, pt.x))

  // transform polar to cartesian coordinates
  def plr2pt(plr: Polar): Point =
    Point(plr.rho * cos(plr.theta), plr.rho * sin(plr.theta))
}

// the functions dealing with images. we provide a set of useful type
// aliases to make the types more meaningful.
object Images {
  type Value   = Double // intended invariant: 0 ≤ Value ≤ 1
  type Img[A]  = Point => A
  type ImgMask = Img[Boolean]
  type ImgGray = Img[Value]
  type ImgClr  = Img[Colour]

  // interpolate between two colours; 0 ≤ w ≤ 1 is the weight of the
  // first colour and (1-w) is the weight of the second colour
  def lerpClr(w: Value, c1: Colour, c2: Colour): Colour = {
    def h(v1: Value, v2: Value) = (w*v1) + ((1-w)*v2)
    Colour(h(c1.R,c2.R), h(c1.G,c2.G), h(c1.B,c2.B), h(c1.alpha,c2.alpha))
  }

  // overlay one colour with another, blending them together
  def overlayClr(c1: Colour, c2: Colour): Colour = {
    def h(v1: Value, v2: Value) = v1 + ((1-c1.alpha)*v2)
    Colour(h(c1.R,c2.R), h(c1.G,c2.G), h(c1.B,c2.B), h(c1.alpha,c2.alpha))
  }

  // we will define a set of "lifting" methods called lift<N> that
  // take functions on <N> values as arguments and return functions on
  // <N> images, where <N> is some number. these lifting methods will
  // enable us to easily create functions to transform and combine <N>
  // images based on functions to transform and combine <N>
  // values. These methods are generic, meaning that the types of the
  // values and images are not specified explicitly, instead they use
  // type variables.
  //
  // Example application: given a function with signature:
  //
  // (Boolean, Value) => Colour
  //
  // ...we could use lift2 to create a function taking
  // an ImgMask and an ImgGray as arguments and returning an ImgClr.


  // Define a generic method named 'lift0' that:
  // -Takes a value of some type
  // -Returns an image containing only that value
  // !!FILL ME IN
  def lift0[A](a: A): Img[A] = (pt: Point) => a


  // Define a curried generic method named 'lift1' that:
  // -Takes a function from a value of type A to a value of type B, and
  // -Takes a image parameterized by type A
  // -Returns an image parameterized by type B
  // !!FILL ME IN
  def lift1[A, B](function: A => B)(img: Img[A]): Img[B] = (pt: Point) => function(img(pt))


  // Define a curried generic method named 'lift2' that:
  // -Takes a function from two values of types A and B to a value of type C, and
  // -Takes an image parameterized by type A, and
  // -Takes an image parameterized by type B, and
  // -Returns an image parameterized by type C
  // !!FILL ME IN
  def lift2[A, B, C](function: (A, B) => C)(imgA: Img[A])(imgB: Img[B]): Img[C] = (pt: Point) => function(imgA(pt), imgB(pt))


  // Define a curried generic method named 'lift3' that:
  // -Takes a function from three values of types A, B, and C to a value of type D, and
  // -Takes an image parameterized by type A, and
  // -Takes an image parameterized by type B, and
  // -Takes an image parameterized by type C, and
  // -Returns an image parameterized by type D
  // !!FILL ME IN
  def lift3[A, B, C, D](function: (A, B, C) => D)(imgA: Img[A])(imgB: Img[B])(imgC: Img[C]) = 
    (pt: Point) => function(imgA(pt), imgB(pt), imgC(pt))

  // Define a function 'lerpImgClr' that uses `lerpClr` (defined above)
  // and one of the above lifting methods to interpolate between two
  // colour images.
  // !!FILL ME IN
  val lerpImgClr = lift3(lerpClr) _


  // Define a function 'overlayImgClr' that uses `overlayClr` (defined
  // above) and one of the above lifting methods to overlay one colour
  // image on top of another
  // !!FILL ME IN
  val overlayImgClr = lift2(overlayClr) _

  // Define a function 'selectImgClr' that uses one of the above
  // lifting methods on an anonymous function that takes a Boolean and
  // two Colours as arguments and returns the first colour if the
  // boolean is true, otherwise the second colour; thus yielding a
  // function that takes an ImgMask and two ImgClrs and returns an
  // ImgClr whose values come from either the first or second ImgClr
  // argument based on the boolean value at that position given by the
  // ImgMask argument.
  // !!FILL ME IN
  val selectImgClr = lift3((bool: Boolean, first: Colour, second: Colour) => if(bool) first else second) _

  // Define a function 'msk2clr' that uses one of the lifting methods
  // on an anonymous function; thus yielding a function that takes a
  // ImgMask as argument and returns an ImgClr where a true value in
  // the ImgMask is black in the ImgClr and a false value is white.
  // !!FILL ME IN
  val msk2clr = lift1((bool: Boolean) => if(bool) black else white) _

  // Define a function 'gray2clr' that uses one of the lifting methods
  // on an anonymous function; thus yielding a function that takes a
  // ImgGray as argument and returns an ImgClr where a Value in the
  // ImgGray is turned into a corresponding Colour in the ImgClr.
  // !!FILL ME IN
  val gray2clr = lift1((value: Value) => Colour(value, value, value, 1)) _
}

// the functions dealing with spatial transforms on images. we provide
// a set of useful type aliases to make the types more meaningful.
object SpatialTransforms {
  type TransformPt  = Point => Point
  type TransformPlr = Polar => Polar
  type Filter[A]    = Img[A] => Img[A]
  type FiltMask     = Filter[Boolean]
  type FiltGray     = Filter[Value]
  type FiltColour   = Filter[Colour]

  // Define a method named 'translatePt' that:
  // -Takes a Vector, and
  // -Returns a TransformPt that translates a point according
  //  to the given Vector.  Recall that to translate a point
  //  by a vector, you add the vector's X component to the point's
  //  X coordinate and the vector's Y component to the point's
  //  Y coordinate.
  // !!FILL ME IN
  def translatePt(vec: Vector): TransformPt = (pt: Point) => Point(vec.x + pt.x, vec.y + pt.y)

  // Define a method named 'scalePt' that:
  // -Takes a Vector, and
  // -Returns a TransformPt that scales a point according to the
  //  given Vector.  Recall that to scale a point by a vector,
  //  you multiply the vector's X component by the point's X
  //  coordinate and the vector's Y component by the point's Y
  //  coordinate.
  // !!FILL ME IN
  def scalePt(vec: Vector): TransformPt = (pt: Point) => Point(vec.x * pt.x, vec.y * pt.y)
    
  // Define a method named 'rotatePt' that:
  // -Takes a Double specifying an angle, and
  // -Returns a TransformPt that rotates a point by the given angle.
  //  Recall that to rotate a point (x, y) by an angle theta, the
  //  new point is:
  //  (x * cos(theta) - y * sin(theta),
  //   y * cos(theta) + x * sin(theta))
  // !!FILL ME IN
  def rotatePt(ang: Double): TransformPt = (pt: Point) => Point(pt.x * cos(ang) - pt.y * sin(ang), pt.y * cos(ang) + pt.x * sin(ang))

  // Define a method named 'swirlPt' that:
  // -Takes a Double specifying an angle, and
  // -Returns a TransformPt that swirls a point by the given angle.
  //  Recall that to swirl a point pt by an angle
  //  theta, the point is rotated by the angle (|pt| * (2*pi/theta)),
  //  where |pt| is the distance from pt to the origin.  You may find
  //  the dist and rotatePt methods useful here.
  // !!FILL ME IN
  def swirlPt(ang: Double): TransformPt = (pt: Point) => Point(pt.x * cos((dist(pt) * (2 * PI / ang))) - pt.y * sin((dist(pt) * (2 * PI / ang))), pt.y * cos((dist(pt) * (2 * PI / ang))) + pt.x * sin((dist(pt) * (2 * PI / ang))))


  // Define a method named 'polarXf' that:
  // -Takes a TransformPlr, and
  // -Returns a TransformPt.  You may find some other methods
  //  helpful here.
  // !!FILL ME IN
  def polarXf(plr: TransformPlr): TransformPt = (pt: Point) => plr2pt(plr(pt2plr(pt)))


  // NOTE: the above transformations work somewhat
  // counter-intuitively, e.g., scalePt(Vector(2,2)) actually scales
  // points so an image is half the size instead of twice the size,
  // and translatePt(Vector(1,0)) actually translates an image to the
  // left instead of to the right. the reason is because of the way we
  // are defining images as functions and transformations as functions
  // on functions; in general, to get the transformation we
  // intuitively expect we must use the inverse transformation on the
  // image. to make this easier, we'll define below versions of the
  // above transformations that automatically use the inverse argument
  // so that we get the results we expect.

  // Define a generic method named 'translate' that:
  // -Takes a Vector, and
  // -Returns a Filter that translates an image with translatePt using
  //  the negation of the provided vector
  // !!FILL ME IN
  def translate[A](vec: Vector): Filter[A] = (img: Img[A]) => (pt: Point) => img(translatePt(vec.neg)(pt))

  // Define a generic method named 'scale' that:
  // -Takes a Vector, and
  // -Returns a Filter that scales an image with scalePt
  //  using the inverse of that vector.
  // !!FILL ME IN
  def scale[A](vec: Vector): Filter[A] = (img: Img[A]) => (pt: Point) => img(scalePt(vec.inverse)(pt))

  // Define a generic method named 'rotate' that:
  // -Takes a Double representing an angle, and
  // -Returns a Filter that rotates an image with rotatePt using
  //  the negation of that angle.
  // !!FILL ME IN
  def rotate[A](ang: Double): Filter[A] = (img: Img[A]) => (pt: Point) => img(rotatePt(-ang)(pt))

  // Define a generic method named 'swirl' that:
  // -Takes a Double representing an angle, and
  // -Returns a Filter that swirls an image with swirlPt using
  //  the negation of that angle.
  // !!FILL ME IN
  def swirl[A](ang: Double): Filter[A] = (img: Img[A]) => (pt: Point) => img(swirlPt(-ang)(pt))

}

// the functions dealing with mask algebra, i.e., combining boolean
// images in various ways to create masks to use for transforming
// other images.
object Masking {
  // Define a function named 'fullM' using one of the lift methods
  // from Images; thus yielding an ImgMask that is always true at
  // every point.
  // !!FILL ME IN
  val fullM: ImgMask = lift0(true)


  // Define a function named 'emptyM' using one of the lift methods
  // from Images; thus yielding an ImgMask that is always false at
  // every point.
  // !!FILL ME IN
  val emptyM: ImgMask = lift0(false)


  // Define a function named 'notM' using one of the lift methods from
  // Images; thus yielding a function that returns the negation of its
  // input: taking an ImgMask as argument and returning an ImgMask
  // whose value at a position is true iff the argument's value at
  // that position was false.
  // !!FILL ME IN
  val notM: ImgMask => ImgMask = lift1((bool: Boolean) => !bool) _


  // Define a function named 'intersectM' using one of the lift
  // methods from Images; thus yielding a function that returns the
  // intersection of its two inputs: taking two ImgMasks as arguments
  // and returning an ImgMask whose value at a position is true iff
  // both argument's values at that position were true.
  // !!FILL ME IN
  val intersectM: ImgMask => ImgMask => ImgMask = lift2((bool1: Boolean, bool2: Boolean) => bool1 && bool2) _


  // Define a function named 'unionM' using one of the lift methods
  // from Images; thus yielding a function that returns the union of
  // its two inputs: taking two ImgMasks as arguments and returning an
  // ImgMask whose value at a position is true if either argument's
  // value at that position was true.
  // !!FILL ME IN
  val unionM: ImgMask => ImgMask => ImgMask = lift2((bool1: Boolean, bool2: Boolean) => bool1 || bool2) _


  // Define a function named 'xorM' using one of the lift methods from
  // Images; thus yielding a function that returns the XOR of its two
  // inputs: taking two ImgMasks as arguments and returning an ImgMask
  // whose value at a position is true if exactly one argument's value
  // at that position was true.
  // !!FILL ME IN
  val xorM: ImgMask => ImgMask => ImgMask = lift2((bool1: Boolean, bool2: Boolean) => (bool1 || bool2) && !(bool1 && bool2)) _


  // Define a function named 'diffM' in terms of a subset of
  // the above defined functions (i.e., diffM is defined as a
  // combination of other masking operations) that returns the set
  // difference of its two inputs: taking two ImgMasks X and Y as
  // arguments and returning an ImgMask whose value at a position is
  // true iff that position was true in X but not in Y.
  // !!FILL ME IN
  val diffM: ImgMask => ImgMask => ImgMask = (maskX: ImgMask) => (maskY: ImgMask) => intersectM(maskX)(notM(maskY))

}


//——————————————————————————————————————————————————————————————————————————————
// GUI implementation

// relation between the GUI canvas coordinate system and the image
// coordinate system. in the canvas coordinate system, (0, 0) is the
// top-left and (canvasWidth-1, canvasHeight-1) is the bottom-right of
// the GUI window. note that the image origin coordinates can be
// negative and/or greater than the canvas width/height.
case class Coord(
  canvasWidth:Int,  // width of the GUI canvas
  canvasHeight:Int, // height of the GUI canvas
  originX:Int,      // canvas X coordinate of the image's origin point
  originY:Int,      // canvas Y coordinate of the image's origin point
  imgWidth:Double,  // the width of the image to fit inside the canvas
  imgHeight:Double  // the height of the image to fit inside the canvas
) {
  // sanity check
  assert(canvasWidth > 0 && canvasHeight > 0)
  assert(imgWidth > 0 && imgHeight > 0)

  // scaling factor from canvas to image coordinates
  val scaleX = canvasWidth.toDouble / imgWidth.toDouble
  val scaleY = canvasHeight.toDouble / imgHeight.toDouble

  // given coordinates (x, y) in the canvas coordinate system, return
  // the corresponding point in the image coordinate system
  def c2img(x:Int, y:Int): Point =
    Point((x - originX)/scaleX, (y - originY)/scaleY)

  def foreachPoint(f: (Int, Int) => Unit) {
    0.until(canvasWidth).foreach(x =>
      0.until(canvasHeight).foreach(y =>
        f(x, y)))
  }
}

abstract class ImgGUI(val coord: Coord) {
  import java.awt.image.BufferedImage

  // begin abstract members
  def namePrefix(): String
  def frameName(): String
  def imgPaint(g: Graphics2D): Unit
  // end abstract members

  lazy val canvas: Panel = {
    new Panel {
      override def paint(g: Graphics2D) {
        imgPaint(g)
      }
      preferredSize = new Dimension(coord.canvasWidth,
                                    coord.canvasHeight)
    }
  }

  lazy val frame: MainFrame = {
    new MainFrame {
      title = frameName
      contents = canvas
    }
  }

  def save(toDir: String, name: String) {
    import javax.imageio.ImageIO

    val image =
      new BufferedImage(
        coord.canvasWidth,
        coord.canvasHeight,
        BufferedImage.TYPE_INT_ARGB)
    canvas.paint(image.getGraphics.asInstanceOf[Graphics2D])
    ImageIO.write(image, "png", new java.io.File(toDir + "/" + namePrefix + name + ".png"))
  }

  // call this to actually display the image on the screen
  def show() {
    frame.open()
  }
} // ImgGUI

// a GUI window to display mask images
class ImgMaskGUI(coord:Coord, val img:ImgMask) extends ImgGUI(coord) {
  def namePrefix(): String = "mask"
  def frameName(): String = "Mask Image"
  def imgPaint(g: Graphics2D) {
    g.setPaint(Color.black)
    coord.foreachPoint((x, y) => {
      if (img(coord.c2img(x, y))) {
        g.drawLine(x, y, x, y)
      }
    })
  }
} // ImgMaskGUI

// a GUI window to display grayscale images
class ImgGrayGUI(coord:Coord, val img:ImgGray) extends ImgGUI(coord) {
  def namePrefix(): String = "gray"
  def frameName(): String = "Grayscale Image"
  def imgPaint(g: Graphics2D) {
    coord.foreachPoint((x, y) => {
      val v = img(coord.c2img(x,y)).toFloat
      g.setPaint(new Color(v, v, v, 1))
      g.drawLine(x, y, x, y)
    })
  }
}

// a GUI window to display colour images
class ImgClrGUI(coord:Coord, val img:ImgClr) extends ImgGUI(coord) {
  def namePrefix(): String = "clr"
  def frameName(): String = "Colour Image"
  def imgPaint(g: Graphics2D) {
    coord.foreachPoint((x, y) => {
      val Colour(r, gg, b, alpha) = img(coord.c2img(x, y))
      g.setPaint(new Color(r.toFloat, gg.toFloat, b.toFloat, alpha.toFloat))
      g.drawLine(x, y, x, y)
    })
  }
}
