</
  define p: input$=3;
  define q: output$=25;
  define r: output$=24;
  
  alw(!(p and !q and som(q)) or (alw(!r);next (q)))
/>