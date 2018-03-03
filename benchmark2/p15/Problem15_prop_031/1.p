</
  define p: output$=21;
  
  (alw(!p); next( (alw(p); next( (alw(!p);next ( (alw(p); next(alw(!p))) or alw(p))) or alw(!p) )) or alw(p) )) or alw(!p)
/>