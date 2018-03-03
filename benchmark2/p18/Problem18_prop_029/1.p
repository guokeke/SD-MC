</
  define p: input$=5;
  define q: input$=4;
  define r: output$=23;
  
  alw(!(p and !q and som(q)) or (alw(!r);next q))
/>