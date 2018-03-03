</
  define p: output$=25;
  
  (alw(!p); next( (alw(p); next( (alw(!p);next ( (alw(p); next(alw(!p))) or alw(p))) or alw(!p) )) or alw(p) )) or alw(!p)
/>
