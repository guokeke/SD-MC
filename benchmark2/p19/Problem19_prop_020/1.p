</
  define p: output$=22;
  
  (alw(!p); next( (alw(p); next( (alw(!p);next ( (alw(p); next(alw(!p))) or alw(p))) or alw(!p) )) or alw(p) )) or alw(!p)
/>