{-# LANGUAGE MultiParamTypeClasses #-}
module OpenGames where
{-
2017-03-29: Meeting on dependently typed decision theories:

* Nicola Botta     PIK            https://www.pik-potsdam.de/members/botta
* Cezar Ionescu    Oxford         https://www.conted.ox.ac.uk/profiles/cezar-ionescu
* Patrik Jansson   Chalmers       https://www.chalmers.se/en/Staff/Pages/patrik-jansson.aspx
* Pierre Lescanne  ENS-Lyon       https://perso.ens-lyon.fr/pierre.lescanne/
* Jules Hedges     Oxford         https://www.cs.ox.ac.uk/people/julian.hedges/
* Viktor Winschel  Oicos.org      https://www.vikwin.de/
* Philipp Zahn     U. St. Gallen  http://www.philipp-zahn.com/

Before lunch: Jules presenting "Open Games". Patrik coding.

Starting from a category of lenses ("outlaw lenses";-).

A category of pairs of sets (the objects are pairs of sets).

morphism:

  (X, S) --(v,u)-> (Y, R)

  v : X -> Y
  u : X x R -> S

-}

data L x s y r = L {view :: x -> y, update :: (x,r) -> s}

compose :: L y r z q -> L x s y r -> L x s z q
compose (L v2 u2) (L v1 u1) = L (v2 . v1) up3
  where up3 (x, q) = u1 (x, u2 (v1 x, q))

idL :: L x s x s
idL = L id snd

example :: L (x1, x2) (x1', x2) x1 x1'
example = L fst (\((_,x2),x') -> (x',x2))

end :: L x x () b
end = L (const ()) fst
-- traditionally called epsilon_x anb b=()

-- normally you would have r=()
lift :: (x -> y) -> L x () y r
lift f = lift2 f (const ())

-- normally you would have x=()
liftOp :: (r -> s) -> L x s () r
liftOp g = lift2 (const ()) g

lift2 :: (x -> y) -> (r -> s) -> L x s y r
lift2 f g = L f (g.snd)

cross f g (x, y) = (f x, g y)

parComp :: L x1 s1 y1 r1 -> L x2 s2 y2 r2 ->
           L (x1, x2) (s1, s2) (y1, y2) (r1, r2)
parComp (L v1 u1) (L v2 u2) = L vboth uboth
  where  vboth = cross v1 v2
         uboth ((x1, x2), (r1, r2)) = (u1 (x1, r1), u2 (x2, r2))

-- Next category
-- Same objects: pairs of sets

type Rel a = a -> a -> Bool
idRel :: Eq a => a -> a -> Bool
idRel = (==)
(&&.) :: Rel a -> Rel b -> Rel (a, b)
p &&. q = \(a1, b1) (a2, b2) -> p a1 a2 && q b1 b2

-- Arrows from (x,s) to (y,r) have type Sigma Set (OG x s y r)
--   where Sigma X Y is the dependent sum type.


data OG x s y r sigma = OG (sigma -> L x s y r)
                           -- ~= (x, y -> r) -> Rel sigma
                           ((L () () x s, L y r () ()) -> Rel sigma)
  -- sigma is a set of strategy profiles and should be the first component in OG

-- Smart constructor
og :: (sigma -> L x s y r) -> ((x, y->r) -> Rel sigma) -> OG x s y r sigma
og p b' = OG p b
  where b (h, k) = b' (convX1 h, convY1 k)

convX1 :: L () () x s -> x
convX2 :: x -> L () () x s
convX1 h = view h ()
convX2 x = L (const x) (const ())

convY1 :: L y r () () -> (y -> r)
convY2 :: (y -> r) -> L y r () ()
convY1 k = \x -> update k (x,())
convY2 f = L (const ()) (f . fst)

play :: OG x s y r sigma -> (sigma, x) -> y
play (OG p _b) (sigma, x) = view (p sigma) x

coplay :: OG x s y r sigma -> (sigma, (x, r)) -> s
coplay (OG p _b) (sigma, xr) = update (p sigma) xr

embed :: L x s y r -> OG x s y r ()
embed l = OG (const l) (const idRel)

idOG :: OG x s x s ()
idOG = embed idL

compOG :: OG y r z q s2 -> OG x s y r s1 -> OG x s z q (s2, s1)
compOG (OG p2 b2) (OG p1 b1) = OG p3 b3
  where  p3 (s2, s1) = compose (p2 s2) (p1 s1)
         b3 (h, k) = \(s2,s1) (s2', s1') ->  b1 (h, compose k (p2 s2)) s1 s1' &&
                                             b2 (compose (p1 s1) h, k) s2 s2'

-- swapOG :: OG x s s x sigma
-- swapOG = embed swapL

{-

Botta: a game contains more than just a game, but also a sort of
solution to the game.

Jules: the solution concept is here tied to Nash equilibrium.

At the top level a "game" is an open game with all parameters set to ()

What is a "strategy profile"? Classically: a function from states
to actions. (Where state often contains the full history.)

Discussion about relation between finite and infinite horizon
decision theories.

Some examples

X ->   -> Y
S <- G <- R

-}

-- This "lifts a selection function" (the |Argmax y r| dictionary) to
-- an open game. Read r as rewards, x as states, y as controls
player :: Argmax y r => OG x () y r (x->y)
player = og lift b
  where b (h, k) _ si = si h `isIn` argmax k

-- Let's generalise from actual "argmax" to something of that type.
class Argmax x r where
  argmax :: (x->r) -> Set x

----------------
-- Example (unfinished)

-- d1 :: OG () () x r x
-- d1 =

-- d2 :: OG x  () y r (x->y)
-- d2 =

utility :: ((x,y)->(r,r)) -> OG (x,y) () (r,r) () ()
utility = embed . lift

counit :: OG s s () ()  ()
counit = embed end

{-

Jules: This theory only supports deterministic games - not with
probabilities (except for a few special cases).

-}


----------------
{-

Viktor:

Econometrics - build models from data. Often used by modellers.

Econometric agents - agents who themselves build models from data.

s -> x -> (y, s)  =  s -> F s
  where  F s = x -> (y, s)

Summary:

There does not seem to be any fundamental difference between
"econometric agents" and other agents - you just provide them with the
information they need.

-}

----------------

{-

Jules: tying it all together

S - states
A - actions
u : (S, A) -> Real  -- utility function
q : (S, A) -> S     -- state transition

Combined into

qu : (S, A) -> (S, R) --  (Mealy machine)
0 < beta < 1

pi : S -> A     -- policy

perhaps also a starting state s0 : S

-}

iter :: Num r => ((s, a) -> (s, r)) -> s -> [a] -> [(s,r)]
iter qu s0 (a:as) = (s0, r0) : iter qu s1 as
  where (s1, r0) = qu (s0, a)

{-
type Stream = []
util :: ([s], [a]) -> [Rational]
util (s:s, a:as) = discounted sums
  -- think of [Rational] as the co-algebraic structure of Reals
-}

beta :: Fractional r => r
beta = 9/10

liftG :: (Argmax a r, Fractional r) => ((s, a) -> (s, r)) -> OG s r s r (s -> a)
liftG qu = og p b
  where  q = fst . qu; u = snd . qu
         play   pi  s      =  q (s, pi s)
         coplay pi (s, r)  =  u (s, pi s) + beta*r
         p pi = L (play pi) (coplay pi)
         b (s, k) _pi' pi  =  pi s `isIn`
                              argmax (\a->coplay pi ((id&&&k) (q (s, a))))

{-

Next step is to define a co-inductive open game

Top level input:  s
Top level output: r

-}

liftH ::  (Argmax a r, Fractional r) =>
          ((s, a) -> (s, r)) -> OG s r () () (s->a)
liftH qu = h
  where  h = reindex dup (compOG h g)
         g = liftG qu

reindex :: (si2 -> si1) -> OG x s y r si1 -> OG x s y r si2
reindex f (OG p b) = OG p' b'
  where  p' = p . f
         b' xf s2 s2' = b xf (f s2) (f s2')


-- --------------
-- Utlities

(&&&) :: (a->b) -> (a->c) -> a -> (b, c)
(f &&& g) x = (f x, g x)

dup :: a -> (a, a)
dup x = (x, x)

-- just for type checking
type Set a = a->Bool

isIn :: a -> Set a -> Bool
isIn x s = s x
