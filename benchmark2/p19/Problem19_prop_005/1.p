</
  define p: output$=23;
  define q: input$=3;
  define r: output$=22;
  
  alw(!(p and !q and som(q)) or (alw(!r);next q))
/>