</
  define p: output$=21;
  define q: output$=23;
  
  !som(p) or (alw(!q and !p); next(p or (alw(q and !p); next(p or (alw(!q and !p);next (p or (alw(q and !p);next(p or (alw(!q);next p)))))))))
/>
