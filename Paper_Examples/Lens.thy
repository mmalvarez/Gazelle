theory Lens imports Main
begin

locale lens =
	fixes get :: "'b => 'a"
	fixes put :: "'a => 'b => 'b"
	
	assumes get_put :
		"\<forall> (a :: 'a) (b :: 'b) . get (put a b) = a"
	assumes put_get :
		"\<forall> (b :: 'b) . put (get b) b = b"
	assumes put_put :
		"\<forall> (a1 :: 'a) (a2 :: 'a) (b :: 'b) .
			put a2 (put a1 b) = put a2 b"


definition (in lens)
	lens_lift :: "('syn => 'a => 'a) => ('syn => 'b => 'b)" where
"lens_lift f syn st =
	(put (f syn (get st)) st)"


end