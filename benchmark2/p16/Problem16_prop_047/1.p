</
  define p: output$=23;
  define q: output$=24;
  
  !som(p) or (alw(!q and !p); next(p or (alw(q and !p); next(p or (alw(!q and !p);next (p or (alw(q and !p);next(p or (alw(!q);next p)))))))))
/>