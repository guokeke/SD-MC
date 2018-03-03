</
  define p: output$=26;
  define q: output$=21;
  
  !som(p) or (alw(!q and !p); next(p or (alw(q and !p); next(p or (alw(!q and !p);next (p or (alw(q and !p);next(p or (alw(!q);next p)))))))))
/>