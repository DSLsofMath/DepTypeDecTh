module OpenGames where
{-
2017-03-29: Meeting on dependently typed decision theories
* Nicola Botta     PIK
* Cezar Ionescu    Oxford
* Patrik Jansson   Chalmers
* Pierre Lescanne  ENS-Lyon
* Jules Hedges     QMUL
* Viktor Winschel
* Philipp Zahn

Before lunch: Jules presenting "Open Games". Patrik coding.
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
-- epsilon_X

lift :: (x -> y) -> L x () y ()
lift f = lift2 f (id :: () -> ())

liftOp :: (r -> s) -> L () s () r
liftOp g = lift2 (id :: () -> ()) g

lift2 :: (x -> y) -> (r -> s) -> L x s y r
lift2 f g = L f (g.snd)

cross f g (x, y) = (f x, g y)

parComp :: L x1 s1 y1 r1 -> L x2 s2 y2 r2 ->
           L (x1, x2) (s1, s2) (y1, y2) (r1, r2)
parComp (L v1 u1) (L v2 u2) = L vboth uboth
  where  vboth = cross v1 v2
         uboth ((x1, x2), (r1, r2)) = (u1 (x1, r1), u2 (x2, r2))

-- Next category

type Rel a = a -> a -> Bool
                                               -- ~= (x, y -> r) -> Rel sigma
data OG x s y r sigma = OG (sigma -> L x s y r) ((L () () x s, L y r () ()) -> Rel sigma)
  -- sigma is a set of strategy profiles and should be the first component in OG


play :: OG x s y r sigma -> (sigma, x) -> y
play (OG p _b) (sigma, x) = view (p sigma) x

coplay :: OG x s y r sigma -> (sigma, (x, r)) -> s
coplay (OG p _b) (sigma, xr) = update (p sigma) xr

idOG :: OG x s x s ()
idOG = embed idL

embed :: L x s y r -> OG x s y r ()
embed l = OG (const l) (const idRel)

idRel :: Eq a => a -> a -> Bool
idRel = (==)

compOG :: OG y r z q s2 -> OG x s y r s1 -> OG x s z q (s2, s1)
compOG (OG p2 b2) (OG p1 b1) = OG p3 b3
  where  p3 (s2, s1) = compose (p2 s2) (p1 s1)
         b3 (h, k) = \(s2,s1) (s2', s1') ->  b1 (h, compose k (p2 s2)) s1 s1' &&
                                             b2 (compose (p1 s1) h, k) s2 s2'

(&&&) :: Rel a -> Rel b -> Rel (a, b)
p &&& q = \(a1, b1) (a2, b2) -> p a1 a2 && q b1 b2

-- Botta: a game contains more than just a game, but also a sort of
-- solution to the game.

-- Jules: the solution concept is here tied to Nash equilibrium.



-- At the top level a "game" is an open game with all parameters set to ()


-- What is a "strategy profile"? Classically: a function from states to actions. (Where state often contains the full history.)

-- Discussion about relation between finite and infinite horizon decision theories.
