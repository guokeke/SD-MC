</
  define p: input$=3;
  define q: input$=2;
  define r: output$=22;
  
  alw(!(p and !q and som(q)) or (alw(!r);next q))
/>