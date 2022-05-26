#lang scribble/base

@; Assigment 1 -------------------
@; Gavin Gray, ETH Zuerich
@; Automated Software Testing
@; Spring 2022, 05.2022

@(require scribble/manual
          scribble-abbrevs/latex
          scribble-abbrevs/manual
          scriblib/autobib
          @; scribble-math
          racket/file
          racket/draw
          racket/class
          scriblib/figure
          pict
          pict/balloon)

@; Utilities

@(define (input-code-file path #:lang [lang 'scheme])
    (define fs (file->string path))
    (define d (cond [(eq? lang 'scheme)
                        (typeset-code fs #:line-numbers 0
                                         #:context #'here)]
                    [else (verbatim fs #:indent 2)]))
    (filebox path d))

@(define-syntax question
    (syntax-rules (n)
        [(_ n v txt ...)
            (elem #:style "noindent"
                  (bold (string-append "Q" (number->string v) " : "))
                  (italic txt ...))]
        [(_ txt ...)
            (elem #:style "noindent"
                  (bold "Q: ")
                  (italic txt ...))]))

@(define-syntax-rule (answer txt ...)
    @;"hangindent=0.4cm"
    (para #:style #f txt ...))

@(define-syntax-rule (section-non flows ...)
    @(section #:style 'hidden-number flows ...))

@; Citation syntax for inserting into bibliography
@(define-cite ~cite citet generate-bibliography
              #:style number-style)

@title[#:style #false]{CS 420 Exam Question}

@author{Gavin Gray}

@question{Assume that in order to add floating-point values to L@subscript{3}, we decided to increase the size of basic values to 64 bits,
          and switch to NaN-tagging. Describe how L@subscript{3} values (both the existing ones as well as 64-bits floating-point values)
          would be represented in such a scheme. For simplicity, assume that primitives working on floating-point values are
          distinct from those working on integers (e.g. integer addition would be @code|{@+}| like now, but floating-point
          addition would be @code|{@float-+}|).}

@(hspace 15)

@;{
@; Floating Point Layout ===
@;
@; The IEEE Standard for Floating-Point Arithmetic (latest IEEE 754-2019)
@; specifies that bits are allocated as follows for a 64 bit word:
@; - 1-bit sign (S)
@; - 11-bit biased exponent (E)
@; - 52-bit trailing significand (T)
@;
@; The specification states that if the exponent bits are all 1, this signifies a "special value" of either:
@; - NaN : Any fractional bit is 1.
@; - [+|-] Infinity : the entire payload is filled with 0.
@;
@; Vocabulary:
@; "trailing significand field"
@; "biased exponent field"
@; ""
@;
@;
@; L3 ===
@;
@; There are (3?) XXX types in L3 :
@; - [new] Floats
@; - Integers
@; - Pointers
@; TODO
@;
@; Testing for Floats --
@;
@; Notes --
@; For a 64 bit address, only 48 are used (so ignore the others ).
@;
}

@; TODO create figure ... ?

@(define payload-d (- 64 1 11 1))
@(define tag-d (- payload-d 48))

@(define payload (number->string payload-d))
@(define tag (number->string tag-d))

@; FIXME spacing

I will be following the specification of the IEEE 754-2019 standard@~cite[ieee-754].
As seen in @(figure-ref "fig:bits"), the contents of a single double precision floating-point number has a 1-bit sign (S),
 an 11-bit biased exponent (E), and a 52-bit trailing significand (T) @~cite[(in-bib ieee-754 ", §3.4")].
A NaN value is indicated by setting all bits of E to one and can represent a @italic{quiet NaN}
or @italic{signaling NaN}. For the purposes of NaN tagging in L@subscript{3} we will
always assume quiet NaNs and thus the first (most significant) bit  of T needs to be set to 1.
@(figure-here "fig:bits"
              "An example of the layout of a 64-bit floating-point."
              bits-label)
In L@subscript{3} we need to represent 6 values: double precision floating-point numbers,
integers, pointers, characters, booleans, and the unit value.
We know that floats will take up the full 64 bit word and everything else needs to fit in the
tagged NaN payload. For a tagged NaN we have @payload bits, which is
more than enough to represent all other L@subscript{3} values.

Following the example of x86-64, we will use only the lower 48 bits of our 64 bit address
leaving @tag bits for us to encode the type stored in the actual payload. With these @tag
bits we could encode our types as demonstrated in @(figure-ref "fig:enc").
Observe that a type tag for NaN is explicetly encoded because we also need to
allow NaNs, as well as the other two @italic{special values}: [+/-]∞. However, no
explicit handling is needed for the infinities as they are represented by having all bits of T set to 0.
This differentiates them from tagged NaNs because the quiet bit will not be set.

@(figure "fig:enc"
         "Possible encoding of 3-bit type tags."
         (centered
             (tabular #:style 'block
                       #:column-properties '(left right)
                       #:row-properties '(bottom-border ())
                       (list (list @bold{Value}   @bold{Type Encoding})
                             (list "NaN"           "000")
                             (list "Integer"       "001")
                             (list "Pointer"       "010")
                             (list "Character"     "011")
                             (list "Boolean True"  "100")
                             (list "Boolean False" "101")
                             (list "Unit"          "110")))))

For the sake of normality, I will assume that integers become 32 bits (instead of 31)
even though, theoretically, they could be 48 bits. As before, checking for a word's type
can be done with a simple bitmask and comparison and all other functionality should remain
the same, especially because all floating-point operations will have their own primitives.
As a final example, if you wanted to check if a given word is an integer, you would mask the
most significant 16 bits with the mask @code{#b0111111111111001}, and if the result is the same
then the word is in fact an integer.

@; --------------------------------------------------------------------
@; Bits image drawing :)

@(generate-bibliography)

@(define height 20)
@(define width 6.5)
@(define weight 0.1)

@(define c-red  (make-color 255 69 0 0.15))
@(define c-red-dark  (make-color 255 69 0 0.35))
@(define c-blue (make-color 0 255 255 0.20))
@(define c-green (make-color 50 255 0 0.25))

@(define (make-rect c)
    (filled-rectangle #:draw-border? #true
                      #:border-color "Black"
                      #:border-width weight
                      #:color c
                      width height))

@(define Es (make-rect c-blue))
@(define Ee (make-rect c-green))
@(define Et (make-rect c-red))
@(define Et-dark (make-rect c-red-dark))

@(define (make-segment len shape ch)
    (launder (apply hc-append
                    (for/list [(in-range len)]
                        shape))))

@(define Segs (make-segment 1 Es "S"))
@(define Sege (make-segment 11 Ee "E"))

@(define Segt-p (make-segment 51 Et "T"))

@(define Segt (hc-append (- (/ weight 2)) Et-dark Segt-p))

@(define indices
    (launder
        (apply hc-append (reverse (for/list [(i (in-range 64))]
                    (cc-superimpose (blank width height)
                                    (text (number->string i)
                                          null
                                          5
                                          -55)))))))

@(define bits
    (cb-superimpose
        (blank 100 80)
        (vc-append (frame #:line-width 0.75
                        (hc-append (hc-append (- (/ weight 2)) Segs Sege)
                                      Segt))
                   indices)))

@(define (plate w h t)
    (cc-superimpose (blank w h) @; The minimum space required
                    (text t 'roman 8)))

@(define be 3)

@(define bits-label
    (pin-balloon (wrap-balloon (plate 30 20 "significand (T)") 'sw -8 20 "white" be)

                (pin-balloon (wrap-balloon (plate 30 20 "quiet NaN bit") 'sw -40 20 "white" be)

                            (pin-balloon (wrap-balloon (plate 30 20 "exponent (E)") 'sw -15 20 "white" be)

                                        (pin-balloon (wrap-balloon (plate 30 20 "sign (S)") 'sw -5 20 "white" be)
                                                        bits
                                                        Segs
                                                        ct-find)

                                        Sege
                                        ct-find)

                            Et-dark
                            ct-find)

                Segt
                ct-find))

@; -------------------------------------------------------------------
@; Bibliography Entires

@(define ieee-754
    (make-bib
        #:title    "IEEE Standard for Floating-Point Arithmetic"
        #:date     "2019"
        #:url      "https://ieeexplore.ieee.org/servlet/opac?punumber=8766227"))
