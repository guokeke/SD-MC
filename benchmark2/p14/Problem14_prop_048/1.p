</
  define p: output$=25;
  define q: output$=26;
  
  !som(p) or (alw(!q and !p); next(p or (alw(q and !p);next (p or (alw(!q and !p);next ( p or (alw(q and !p); next (p or (alw(!q);next p)))))))))
/>