</
  define p: output$=24;
  
  (alw(!p); next( (alw(p); next( (alw(!p);next ( (alw(p); next(alw(!p))) or alw(p))) or alw(!p) )) or alw(p) )) or alw(!p)
/>