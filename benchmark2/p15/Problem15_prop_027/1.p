</
  define p: input$=2;
  define q: output$=25;
  
  !som(p) or (alw(!q and !p); next(p or (alw(q and !p);next (p or (alw(!q and !p);next ( p or (alw(q and !p); next (p or (alw(!q);next p)))))))))
/>