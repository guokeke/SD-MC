</
  define p: output$=23;
  
  (alw(!p); next( (alw(p); next( (alw(!p);next ( (alw(p); next(alw(!p))) or alw(p))) or alw(!p) )) or alw(p) )) or alw(!p)
/>